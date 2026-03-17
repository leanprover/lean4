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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "failed with\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SizeOf"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeOf"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(151, 205, 72, 249, 57, 72, 20, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14;
static const lean_array_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_lt_of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(126, 191, 12, 194, 254, 232, 98, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lt_irrefl"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(120, 15, 17, 57, 9, 165, 30, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "succeeded"};
static const lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
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
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
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
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(lean_object* v_cls_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_options_29_; uint8_t v_hasTrace_30_; 
v_options_29_ = lean_ctor_get(v___y_27_, 2);
v_hasTrace_30_ = lean_ctor_get_uint8(v_options_29_, sizeof(void*)*1);
if (v_hasTrace_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_cls_26_);
v___x_31_ = lean_box(v_hasTrace_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v_inheritedTraceOptions_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_inheritedTraceOptions_33_ = lean_ctor_get(v___y_27_, 13);
v___x_34_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___closed__1));
v___x_35_ = l_Lean_Name_append(v___x_34_, v_cls_26_);
v___x_36_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_33_, v_options_29_, v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = lean_box(v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg___boxed(lean_object* v_cls_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(v_cls_39_, v___y_40_);
lean_dec_ref(v___y_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(lean_object* v_cls_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(v_cls_43_, v___y_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(lean_object* v_cls_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(uint8_t v___y_57_, lean_object* v_____r_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(v___y_57_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(lean_object* v___y_67_, lean_object* v_____r_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v___y_8143__boxed_74_; lean_object* v_res_75_; 
v___y_8143__boxed_74_ = lean_unbox(v___y_67_);
v_res_75_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_8143__boxed_74_, v_____r_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(uint8_t v___x_76_, lean_object* v_____r_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_box(v___x_76_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(lean_object* v___x_86_, lean_object* v_____r_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v___x_8170__boxed_93_; lean_object* v_res_94_; 
v___x_8170__boxed_93_ = lean_unbox(v___x_86_);
v_res_94_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_8170__boxed_93_, v_____r_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; lean_object* v_env_102_; lean_object* v___x_103_; lean_object* v_mctx_104_; lean_object* v_lctx_105_; lean_object* v_options_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_101_ = lean_st_ref_get(v___y_99_);
v_env_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_env_102_);
lean_dec(v___x_101_);
v___x_103_ = lean_st_ref_get(v___y_97_);
v_mctx_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_mctx_104_);
lean_dec(v___x_103_);
v_lctx_105_ = lean_ctor_get(v___y_96_, 2);
v_options_106_ = lean_ctor_get(v___y_98_, 2);
lean_inc_ref(v_options_106_);
lean_inc_ref(v_lctx_105_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v_env_102_);
lean_ctor_set(v___x_107_, 1, v_mctx_104_);
lean_ctor_set(v___x_107_, 2, v_lctx_105_);
lean_ctor_set(v___x_107_, 3, v_options_106_);
v___x_108_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_msgData_95_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1(v_msgData_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_117_; double v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_float_of_nat(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(lean_object* v_cls_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_175_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 5);
v___x_130_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__1(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_175_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_175_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_175_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v_traceState_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_cache_141_; lean_object* v_messages_142_; lean_object* v_infoState_143_; lean_object* v_snapshotTasks_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_174_; 
v___x_135_ = lean_st_ref_take(v___y_127_);
v_traceState_136_ = lean_ctor_get(v___x_135_, 4);
v_env_137_ = lean_ctor_get(v___x_135_, 0);
v_nextMacroScope_138_ = lean_ctor_get(v___x_135_, 1);
v_ngen_139_ = lean_ctor_get(v___x_135_, 2);
v_auxDeclNGen_140_ = lean_ctor_get(v___x_135_, 3);
v_cache_141_ = lean_ctor_get(v___x_135_, 5);
v_messages_142_ = lean_ctor_get(v___x_135_, 6);
v_infoState_143_ = lean_ctor_get(v___x_135_, 7);
v_snapshotTasks_144_ = lean_ctor_get(v___x_135_, 8);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_174_ == 0)
{
v___x_146_ = v___x_135_;
v_isShared_147_ = v_isSharedCheck_174_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snapshotTasks_144_);
lean_inc(v_infoState_143_);
lean_inc(v_messages_142_);
lean_inc(v_cache_141_);
lean_inc(v_traceState_136_);
lean_inc(v_auxDeclNGen_140_);
lean_inc(v_ngen_139_);
lean_inc(v_nextMacroScope_138_);
lean_inc(v_env_137_);
lean_dec(v___x_135_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_174_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint64_t v_tid_148_; lean_object* v_traces_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_173_; 
v_tid_148_ = lean_ctor_get_uint64(v_traceState_136_, sizeof(void*)*1);
v_traces_149_ = lean_ctor_get(v_traceState_136_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_traceState_136_);
if (v_isSharedCheck_173_ == 0)
{
v___x_151_ = v_traceState_136_;
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_traces_149_);
lean_dec(v_traceState_136_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; double v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_153_ = lean_box(0);
v___x_154_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__0);
v___x_155_ = 0;
v___x_156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__1));
v___x_157_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_157_, 0, v_cls_122_);
lean_ctor_set(v___x_157_, 1, v___x_153_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
lean_ctor_set_float(v___x_157_, sizeof(void*)*3, v___x_154_);
lean_ctor_set_float(v___x_157_, sizeof(void*)*3 + 8, v___x_154_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*3 + 16, v___x_155_);
v___x_158_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___closed__2));
v___x_159_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v_a_131_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
lean_inc(v_ref_129_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_ref_129_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_PersistentArray_push___redArg(v_traces_149_, v___x_160_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_161_);
v___x_163_ = v___x_151_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_161_);
lean_ctor_set_uint64(v_reuseFailAlloc_172_, sizeof(void*)*1, v_tid_148_);
v___x_163_ = v_reuseFailAlloc_172_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v___x_163_);
v___x_165_ = v___x_146_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_env_137_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_171_, 5, v_cache_141_);
lean_ctor_set(v_reuseFailAlloc_171_, 6, v_messages_142_);
lean_ctor_set(v_reuseFailAlloc_171_, 7, v_infoState_143_);
lean_ctor_set(v_reuseFailAlloc_171_, 8, v_snapshotTasks_144_);
v___x_165_ = v_reuseFailAlloc_171_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_st_ref_set(v___y_127_, v___x_165_);
v___x_167_ = lean_box(0);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_167_);
v___x_169_ = v___x_133_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(lean_object* v_cls_176_, lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_cls_176_, v_msg_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_ks_188_; lean_object* v_vs_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_213_; 
v_ks_188_ = lean_ctor_get(v_x_184_, 0);
v_vs_189_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_213_ == 0)
{
v___x_191_ = v_x_184_;
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_vs_189_);
lean_inc(v_ks_188_);
lean_dec(v_x_184_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_213_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_array_get_size(v_ks_188_);
v___x_194_ = lean_nat_dec_lt(v_x_185_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
lean_dec(v_x_185_);
v___x_195_ = lean_array_push(v_ks_188_, v_x_186_);
v___x_196_ = lean_array_push(v_vs_189_, v_x_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_196_);
lean_ctor_set(v___x_191_, 0, v___x_195_);
v___x_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v_k_x27_200_; uint8_t v___x_201_; 
v_k_x27_200_ = lean_array_fget_borrowed(v_ks_188_, v_x_185_);
v___x_201_ = l_Lean_instBEqMVarId_beq(v_x_186_, v_k_x27_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_203_; 
if (v_isShared_192_ == 0)
{
v___x_203_ = v___x_191_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_ks_188_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_vs_189_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_x_185_, v___x_204_);
lean_dec(v_x_185_);
v_x_184_ = v___x_203_;
v_x_185_ = v___x_205_;
goto _start;
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_array_fset(v_ks_188_, v_x_185_, v_x_186_);
v___x_209_ = lean_array_fset(v_vs_189_, v_x_185_, v_x_187_);
lean_dec(v_x_185_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_209_);
lean_ctor_set(v___x_191_, 0, v___x_208_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_214_, lean_object* v_k_215_, lean_object* v_v_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_214_, v___x_217_, v_k_215_, v_v_216_);
return v___x_218_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; 
v___x_219_ = ((size_t)5ULL);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_shift_left(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; 
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_224_ = lean_usize_sub(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(lean_object* v_x_226_, size_t v_x_227_, size_t v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_es_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v_j_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_es_231_ = lean_ctor_get(v_x_226_, 0);
v___x_232_ = ((size_t)5ULL);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_235_ = lean_usize_land(v_x_227_, v___x_234_);
v_j_236_ = lean_usize_to_nat(v___x_235_);
v___x_237_ = lean_array_get_size(v_es_231_);
v___x_238_ = lean_nat_dec_lt(v_j_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_j_236_);
lean_dec(v_x_230_);
lean_dec(v_x_229_);
return v_x_226_;
}
else
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_es_231_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_x_226_, 0);
lean_dec(v_unused_276_);
v___x_240_ = v_x_226_;
v_isShared_241_ = v_isSharedCheck_275_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_x_226_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_275_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_v_242_; lean_object* v___x_243_; lean_object* v_xs_x27_244_; lean_object* v___y_246_; 
v_v_242_ = lean_array_fget(v_es_231_, v_j_236_);
v___x_243_ = lean_box(0);
v_xs_x27_244_ = lean_array_fset(v_es_231_, v_j_236_, v___x_243_);
switch(lean_obj_tag(v_v_242_))
{
case 0:
{
lean_object* v_key_251_; lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_key_251_ = lean_ctor_get(v_v_242_, 0);
v_val_252_ = lean_ctor_get(v_v_242_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_v_242_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_inc(v_key_251_);
lean_dec(v_v_242_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = l_Lean_instBEqMVarId_beq(v_x_229_, v_key_251_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_del_object(v___x_254_);
v___x_257_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_251_, v_val_252_, v_x_229_, v_x_230_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
v___y_246_ = v___x_258_;
goto v___jp_245_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v_val_252_);
lean_dec(v_key_251_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_x_230_);
lean_ctor_set(v___x_254_, 0, v_x_229_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_x_229_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_x_230_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v___y_246_ = v___x_260_;
goto v___jp_245_;
}
}
}
}
case 1:
{
lean_object* v_node_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_node_263_ = lean_ctor_get(v_v_242_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v_v_242_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_node_263_);
lean_dec(v_v_242_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_267_ = lean_usize_shift_right(v_x_227_, v___x_232_);
v___x_268_ = lean_usize_add(v_x_228_, v___x_233_);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(v_node_263_, v___x_267_, v___x_268_, v_x_229_, v_x_230_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_269_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v___y_246_ = v___x_271_;
goto v___jp_245_;
}
}
}
default: 
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_x_229_);
lean_ctor_set(v___x_274_, 1, v_x_230_);
v___y_246_ = v___x_274_;
goto v___jp_245_;
}
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_array_fset(v_xs_x27_244_, v_j_236_, v___y_246_);
lean_dec(v_j_236_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_298_; 
v_ks_277_ = lean_ctor_get(v_x_226_, 0);
v_vs_278_ = lean_ctor_get(v_x_226_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_298_ == 0)
{
v___x_280_ = v_x_226_;
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_vs_278_);
lean_inc(v_ks_277_);
lean_dec(v_x_226_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_ks_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_vs_278_);
v___x_283_ = v_reuseFailAlloc_297_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v_newNode_284_; uint8_t v___y_286_; size_t v___x_292_; uint8_t v___x_293_; 
v_newNode_284_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5___redArg(v___x_283_, v_x_229_, v_x_230_);
v___x_292_ = ((size_t)7ULL);
v___x_293_ = lean_usize_dec_le(v___x_292_, v_x_228_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_284_);
v___x_295_ = lean_unsigned_to_nat(4u);
v___x_296_ = lean_nat_dec_lt(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
v___y_286_ = v___x_296_;
goto v___jp_285_;
}
else
{
v___y_286_ = v___x_293_;
goto v___jp_285_;
}
v___jp_285_:
{
if (v___y_286_ == 0)
{
lean_object* v_ks_287_; lean_object* v_vs_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_ks_287_ = lean_ctor_get(v_newNode_284_, 0);
lean_inc_ref(v_ks_287_);
v_vs_288_ = lean_ctor_get(v_newNode_284_, 1);
lean_inc_ref(v_vs_288_);
lean_dec_ref(v_newNode_284_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg(v_x_228_, v_ks_287_, v_vs_288_, v___x_289_, v___x_290_);
lean_dec_ref(v_vs_288_);
lean_dec_ref(v_ks_287_);
return v___x_291_;
}
else
{
return v_newNode_284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_299_, lean_object* v_keys_300_, lean_object* v_vals_301_, lean_object* v_i_302_, lean_object* v_entries_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_keys_300_);
v___x_305_ = lean_nat_dec_lt(v_i_302_, v___x_304_);
if (v___x_305_ == 0)
{
lean_dec(v_i_302_);
return v_entries_303_;
}
else
{
lean_object* v_k_306_; lean_object* v_v_307_; uint64_t v___x_308_; size_t v_h_309_; size_t v___x_310_; lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v_h_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_k_306_ = lean_array_fget_borrowed(v_keys_300_, v_i_302_);
v_v_307_ = lean_array_fget_borrowed(v_vals_301_, v_i_302_);
v___x_308_ = l_Lean_instHashableMVarId_hash(v_k_306_);
v_h_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v_depth_299_, v___x_312_);
v___x_314_ = lean_usize_mul(v___x_310_, v___x_313_);
v_h_315_ = lean_usize_shift_right(v_h_309_, v___x_314_);
v___x_316_ = lean_nat_add(v_i_302_, v___x_311_);
lean_dec(v_i_302_);
lean_inc(v_v_307_);
lean_inc(v_k_306_);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(v_entries_303_, v_h_315_, v_depth_299_, v_k_306_, v_v_307_);
v_i_302_ = v___x_316_;
v_entries_303_ = v___x_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_319_, lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_i_322_, lean_object* v_entries_323_){
_start:
{
size_t v_depth_boxed_324_; lean_object* v_res_325_; 
v_depth_boxed_324_ = lean_unbox_usize(v_depth_319_);
lean_dec(v_depth_319_);
v_res_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_324_, v_keys_320_, v_vals_321_, v_i_322_, v_entries_323_);
lean_dec_ref(v_vals_321_);
lean_dec_ref(v_keys_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
size_t v_x_8412__boxed_331_; size_t v_x_8413__boxed_332_; lean_object* v_res_333_; 
v_x_8412__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_x_8413__boxed_332_ = lean_unbox_usize(v_x_328_);
lean_dec(v_x_328_);
v_res_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(v_x_326_, v_x_8412__boxed_331_, v_x_8413__boxed_332_, v_x_329_, v_x_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3___redArg(lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_337_ = l_Lean_instHashableMVarId_hash(v_x_335_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(v_x_334_, v___x_338_, v___x_339_, v_x_335_, v_x_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg(lean_object* v_mvarId_341_, lean_object* v_val_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_mctx_346_; lean_object* v_cache_347_; lean_object* v_zetaDeltaFVarIds_348_; lean_object* v_postponed_349_; lean_object* v_diag_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_377_; 
v___x_345_ = lean_st_ref_take(v___y_343_);
v_mctx_346_ = lean_ctor_get(v___x_345_, 0);
v_cache_347_ = lean_ctor_get(v___x_345_, 1);
v_zetaDeltaFVarIds_348_ = lean_ctor_get(v___x_345_, 2);
v_postponed_349_ = lean_ctor_get(v___x_345_, 3);
v_diag_350_ = lean_ctor_get(v___x_345_, 4);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_377_ == 0)
{
v___x_352_ = v___x_345_;
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_diag_350_);
lean_inc(v_postponed_349_);
lean_inc(v_zetaDeltaFVarIds_348_);
lean_inc(v_cache_347_);
lean_inc(v_mctx_346_);
lean_dec(v___x_345_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_depth_354_; lean_object* v_levelAssignDepth_355_; lean_object* v_mvarCounter_356_; lean_object* v_lDepth_357_; lean_object* v_decls_358_; lean_object* v_userNames_359_; lean_object* v_lAssignment_360_; lean_object* v_eAssignment_361_; lean_object* v_dAssignment_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_376_; 
v_depth_354_ = lean_ctor_get(v_mctx_346_, 0);
v_levelAssignDepth_355_ = lean_ctor_get(v_mctx_346_, 1);
v_mvarCounter_356_ = lean_ctor_get(v_mctx_346_, 2);
v_lDepth_357_ = lean_ctor_get(v_mctx_346_, 3);
v_decls_358_ = lean_ctor_get(v_mctx_346_, 4);
v_userNames_359_ = lean_ctor_get(v_mctx_346_, 5);
v_lAssignment_360_ = lean_ctor_get(v_mctx_346_, 6);
v_eAssignment_361_ = lean_ctor_get(v_mctx_346_, 7);
v_dAssignment_362_ = lean_ctor_get(v_mctx_346_, 8);
v_isSharedCheck_376_ = !lean_is_exclusive(v_mctx_346_);
if (v_isSharedCheck_376_ == 0)
{
v___x_364_ = v_mctx_346_;
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_dAssignment_362_);
lean_inc(v_eAssignment_361_);
lean_inc(v_lAssignment_360_);
lean_inc(v_userNames_359_);
lean_inc(v_decls_358_);
lean_inc(v_lDepth_357_);
lean_inc(v_mvarCounter_356_);
lean_inc(v_levelAssignDepth_355_);
lean_inc(v_depth_354_);
lean_dec(v_mctx_346_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3___redArg(v_eAssignment_361_, v_mvarId_341_, v_val_342_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 7, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_depth_354_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_levelAssignDepth_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_mvarCounter_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_lDepth_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_decls_358_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_userNames_359_);
lean_ctor_set(v_reuseFailAlloc_375_, 6, v_lAssignment_360_);
lean_ctor_set(v_reuseFailAlloc_375_, 7, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 8, v_dAssignment_362_);
v___x_368_ = v_reuseFailAlloc_375_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_368_);
v___x_370_ = v___x_352_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_cache_347_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_zetaDeltaFVarIds_348_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_postponed_349_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_diag_350_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_st_ref_set(v___y_343_, v___x_370_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg___boxed(lean_object* v_mvarId_378_, lean_object* v_val_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg(v_mvarId_378_, v_val_379_, v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_unsigned_to_nat(16u);
v___x_407_ = lean_mk_array(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11);
v___x_416_ = 1;
v___x_417_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_414_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*2, v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_unsigned_to_nat(32u);
v___x_424_ = lean_mk_empty_array_with_capacity(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18(void){
_start:
{
size_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_426_ = ((size_t)5ULL);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_unsigned_to_nat(32u);
v___x_429_ = lean_mk_empty_array_with_capacity(v___x_428_);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
v___x_431_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_427_);
lean_ctor_set(v___x_431_, 3, v___x_427_);
lean_ctor_set_usize(v___x_431_, 4, v___x_426_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18);
v___x_433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13);
v___x_434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
lean_ctor_set(v___x_434_, 3, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19);
v___x_436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(lean_object* v_mvarId_450_, lean_object* v_h_451_, lean_object* v_lhs_452_, lean_object* v_rhs_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_a_460_; lean_object* v___y_478_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v_a_505_; lean_object* v___y_509_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8));
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
lean_inc_ref(v___x_513_);
v___x_514_ = lean_array_push(v___x_513_, v_lhs_452_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_515_ = l_Lean_Meta_mkAppM(v___x_511_, v___x_514_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
lean_inc_ref(v___x_513_);
v___x_517_ = lean_array_push(v___x_513_, v_rhs_453_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_518_ = l_Lean_Meta_mkAppM(v___x_511_, v___x_517_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref(v___x_518_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
lean_inc(v_a_516_);
v___x_520_ = l_Lean_Meta_mkLT(v_a_516_, v_a_519_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = lean_box(0);
lean_inc_ref(v_a_454_);
v___x_523_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_521_, v___x_522_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_457_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; uint8_t v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = lean_unsigned_to_nat(2u);
v___x_528_ = 0;
v___x_529_ = 1;
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9));
lean_inc_ref(v___x_513_);
v___x_532_ = lean_array_push(v___x_513_, v_a_526_);
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14);
v___x_534_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_531_, v___x_532_, v___x_533_, v_a_454_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_Expr_mvarId_x21(v_a_524_);
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15));
v___x_538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_539_ = l_Lean_Meta_simpTarget(v___x_536_, v_a_535_, v___x_537_, v___x_530_, v___x_529_, v___x_538_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_587_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_587_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_587_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_587_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_544_; 
v_fst_544_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_fst_544_);
lean_dec(v_a_540_);
if (lean_obj_tag(v_fst_544_) == 0)
{
lean_object* v___x_545_; 
lean_del_object(v___x_542_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_545_ = l_Lean_Meta_mkEqSymm(v_h_451_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = l_Lean_Expr_appFn_x21(v_a_516_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_548_ = l_Lean_Meta_mkCongrArg(v___x_547_, v_a_546_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23));
v___x_551_ = lean_mk_empty_array_with_capacity(v___x_527_);
v___x_552_ = lean_array_push(v___x_551_, v_a_524_);
v___x_553_ = lean_array_push(v___x_552_, v_a_549_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_554_ = l_Lean_Meta_mkAppM(v___x_550_, v___x_553_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref(v___x_554_);
v___x_556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25));
v___x_557_ = lean_array_push(v___x_513_, v_a_516_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_558_ = l_Lean_Meta_mkAppM(v___x_556_, v___x_557_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v___x_558_);
lean_inc(v_mvarId_450_);
v___x_560_ = l_Lean_MVarId_getType(v_mvarId_450_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref(v___x_560_);
v___x_562_ = l_Lean_Expr_app___override(v_a_559_, v_a_555_);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
v___x_563_ = l_Lean_Meta_mkFalseElim(v_a_561_, v___x_562_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_a_568_; uint8_t v___x_569_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg(v_mvarId_450_, v_a_564_, v_a_455_);
lean_dec_ref(v___x_565_);
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_567_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(v___x_566_, v_a_456_);
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = lean_unbox(v_a_568_);
lean_dec(v_a_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_box(0);
v___x_571_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_529_, v___x_570_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v___y_509_ = v___x_571_;
goto v___jp_508_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27);
v___x_573_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v___x_566_, v___x_572_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
v___x_575_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_529_, v_a_574_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v___y_509_ = v___x_575_;
goto v___jp_508_;
}
else
{
lean_object* v_a_576_; 
v_a_576_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_573_);
v_a_505_ = v_a_576_;
goto v___jp_504_;
}
}
}
else
{
lean_object* v_a_577_; 
lean_dec(v_mvarId_450_);
v_a_577_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_563_);
v_a_505_ = v_a_577_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_578_; 
lean_dec(v_a_559_);
lean_dec(v_a_555_);
lean_dec(v_mvarId_450_);
v_a_578_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_560_);
v_a_505_ = v_a_578_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_579_; 
lean_dec(v_a_555_);
lean_dec(v_mvarId_450_);
v_a_579_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_558_);
v_a_505_ = v_a_579_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec(v_mvarId_450_);
v_a_580_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_554_);
v_a_505_ = v_a_580_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_581_; 
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec(v_mvarId_450_);
v_a_581_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_548_);
v_a_505_ = v_a_581_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_582_; 
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec(v_mvarId_450_);
v_a_582_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_545_);
v_a_505_ = v_a_582_;
goto v___jp_504_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec_ref(v_fst_544_);
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v___x_583_ = lean_box(v___x_528_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_583_);
v___x_585_ = v___x_542_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
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
else
{
lean_object* v_a_588_; 
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_588_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_539_);
v_a_505_ = v_a_588_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_589_; 
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_589_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_534_);
v_a_505_ = v_a_589_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_590_; 
lean_dec(v_a_524_);
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_590_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_525_);
v_a_505_ = v_a_590_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_591_; 
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_591_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_523_);
v_a_505_ = v_a_591_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_592_; 
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_592_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_592_);
lean_dec_ref(v___x_520_);
v_a_505_ = v_a_592_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_593_; 
lean_dec(v_a_516_);
lean_dec_ref(v___x_513_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_593_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_518_);
v_a_505_ = v_a_593_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_594_; 
lean_dec_ref(v___x_513_);
lean_dec_ref(v_rhs_453_);
lean_dec_ref(v_h_451_);
lean_dec(v_mvarId_450_);
v_a_594_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_515_);
v_a_505_ = v_a_594_;
goto v___jp_504_;
}
v___jp_459_:
{
if (lean_obj_tag(v_a_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v_a_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v_a_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v_a_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v_a_460_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_a_460_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v_a_460_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v_a_460_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 0);
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
v___jp_477_:
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___y_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___y_478_);
v_a_460_ = v_a_479_;
goto v___jp_459_;
}
v___jp_480_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_a_485_; uint8_t v___x_486_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_484_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(v___x_483_, v_a_456_);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_unbox(v_a_485_);
lean_dec(v_a_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v___y_481_);
v___x_487_ = lean_box(0);
v___x_488_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_482_, v___x_487_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v___y_478_ = v___x_488_;
goto v___jp_477_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5, &l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5);
v___x_490_ = l_Lean_Exception_toMessageData(v___y_481_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v___x_483_, v___x_491_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_494_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v___x_492_);
v___x_494_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_482_, v_a_493_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v___y_478_ = v___x_494_;
goto v___jp_477_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v_a_495_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_492_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_492_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___y_481_);
return v___x_503_;
}
}
v___jp_504_:
{
uint8_t v___x_506_; 
v___x_506_ = l_Lean_Exception_isInterrupt(v_a_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
lean_inc_ref(v_a_505_);
v___x_507_ = l_Lean_Exception_isRuntime(v_a_505_);
v___y_481_ = v_a_505_;
v___y_482_ = v___x_507_;
goto v___jp_480_;
}
else
{
v___y_481_ = v_a_505_;
v___y_482_ = v___x_506_;
goto v___jp_480_;
}
}
v___jp_508_:
{
lean_object* v_a_510_; 
v_a_510_ = lean_ctor_get(v___y_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___y_509_);
v_a_460_ = v_a_510_;
goto v___jp_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(lean_object* v_mvarId_595_, lean_object* v_h_596_, lean_object* v_lhs_597_, lean_object* v_rhs_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_595_, v_h_596_, v_lhs_597_, v_rhs_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2(lean_object* v_mvarId_605_, lean_object* v_val_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___redArg(v_mvarId_605_, v_val_606_, v___y_608_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2___boxed(lean_object* v_mvarId_613_, lean_object* v_val_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2(v_mvarId_613_, v_val_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3___redArg(v_x_622_, v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, size_t v_x_628_, size_t v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___redArg(v_x_627_, v_x_628_, v_x_629_, v_x_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_9215__boxed_639_; size_t v_x_9216__boxed_640_; lean_object* v_res_641_; 
v_x_9215__boxed_639_ = lean_unbox_usize(v_x_635_);
lean_dec(v_x_635_);
v_x_9216__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4(v_00_u03b2_633_, v_x_634_, v_x_9215__boxed_639_, v_x_9216__boxed_640_, v_x_637_, v_x_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_642_, lean_object* v_n_643_, lean_object* v_k_644_, lean_object* v_v_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5___redArg(v_n_643_, v_k_644_, v_v_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_647_, size_t v_depth_648_, lean_object* v_keys_649_, lean_object* v_vals_650_, lean_object* v_heq_651_, lean_object* v_i_652_, lean_object* v_entries_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_648_, v_keys_649_, v_vals_650_, v_i_652_, v_entries_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_655_, lean_object* v_depth_656_, lean_object* v_keys_657_, lean_object* v_vals_658_, lean_object* v_heq_659_, lean_object* v_i_660_, lean_object* v_entries_661_){
_start:
{
size_t v_depth_boxed_662_; lean_object* v_res_663_; 
v_depth_boxed_662_ = lean_unbox_usize(v_depth_656_);
lean_dec(v_depth_656_);
v_res_663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_655_, v_depth_boxed_662_, v_keys_657_, v_vals_658_, v_heq_659_, v_i_660_, v_entries_661_);
lean_dec_ref(v_vals_658_);
lean_dec_ref(v_keys_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_665_, v_x_666_, v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(lean_object* v_mvarId_670_, lean_object* v_x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_670_, v_x_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_677_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_677_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(lean_object* v_mvarId_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(lean_object* v_00_u03b1_702_, lean_object* v_mvarId_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_703_, v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(lean_object* v_00_u03b1_711_, lean_object* v_mvarId_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(v_00_u03b1_711_, v_mvarId_712_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__2));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* v_h_726_, lean_object* v_mvarId_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc_ref(v_h_726_);
v___x_733_ = lean_infer_type(v_h_726_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
v___x_735_ = l_Lean_Meta_whnfD(v_a_734_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_789_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_789_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_789_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_789_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_a_775_; uint8_t v___x_776_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_774_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___redArg(v___x_773_, v___y_730_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = lean_unbox(v_a_775_);
lean_dec(v_a_775_);
if (v___x_776_ == 0)
{
v___y_741_ = v___y_728_;
v___y_742_ = v___y_729_;
v___y_743_ = v___y_730_;
v___y_744_ = v___y_731_;
goto v___jp_740_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_777_ = lean_obj_once(&l_Lean_MVarId_acyclic___lam__0___closed__3, &l_Lean_MVarId_acyclic___lam__0___closed__3_once, _init_l_Lean_MVarId_acyclic___lam__0___closed__3);
lean_inc(v_a_736_);
v___x_778_ = l_Lean_MessageData_ofExpr(v_a_736_);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v___x_773_, v___x_779_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref(v___x_780_);
v___y_741_ = v___y_728_;
v___y_742_ = v___y_729_;
v___y_743_ = v___y_730_;
v___y_744_ = v___y_731_;
goto v___jp_740_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_738_);
lean_dec(v_a_736_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
v___jp_740_:
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = ((lean_object*)(l_Lean_MVarId_acyclic___lam__0___closed__1));
v___x_746_ = lean_unsigned_to_nat(3u);
v___x_747_ = l_Lean_Expr_isAppOfArity(v_a_736_, v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_a_736_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
v___x_748_ = lean_box(v___x_747_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_748_);
v___x_750_ = v___x_738_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_del_object(v___x_738_);
v___x_752_ = l_Lean_Expr_appFn_x21(v_a_736_);
v___x_753_ = l_Lean_Expr_appArg_x21(v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = l_Lean_Expr_appArg_x21(v_a_736_);
lean_dec(v_a_736_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc_ref(v___x_754_);
lean_inc_ref(v___x_753_);
v___x_755_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_753_, v___x_754_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_unbox(v_a_756_);
lean_dec(v_a_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc_ref(v___x_753_);
lean_inc_ref(v___x_754_);
v___x_758_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(v___x_754_, v___x_753_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; uint8_t v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
v___x_760_ = lean_unbox(v_a_759_);
lean_dec(v_a_759_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_753_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
return v___x_758_;
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v___x_758_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
v___x_761_ = l_Lean_Meta_mkEqSymm(v_h_726_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___x_763_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_727_, v_a_762_, v___x_754_, v___x_753_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_753_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_mvarId_727_);
v_a_764_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_761_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_753_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
return v___x_758_;
}
}
else
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_727_, v_h_726_, v___x_753_, v___x_754_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_772_;
}
}
else
{
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_753_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
v_a_790_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_735_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_735_);
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
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v_mvarId_727_);
lean_dec_ref(v_h_726_);
v_a_798_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_733_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_733_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0___boxed(lean_object* v_h_806_, lean_object* v_mvarId_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_MVarId_acyclic___lam__0(v_h_806_, v_mvarId_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* v_mvarId_814_, lean_object* v_h_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; 
lean_inc(v_mvarId_814_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0___boxed), 7, 2);
lean_closure_set(v___f_821_, 0, v_h_815_);
lean_closure_set(v___f_821_, 1, v_mvarId_814_);
v___x_822_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(v_mvarId_814_, v___f_821_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___boxed(lean_object* v_mvarId_823_, lean_object* v_h_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_MVarId_acyclic(v_mvarId_823_, v_h_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3));
v___x_895_ = 0;
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_));
v___x_897_ = l_Lean_registerTraceClass(v___x_894_, v___x_895_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
return v_res_899_;
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
