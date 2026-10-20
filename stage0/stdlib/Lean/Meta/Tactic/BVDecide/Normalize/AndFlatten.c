// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten
// Imports: public import Std.Tactic.BVDecide.Normalize.Bool public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "and_left"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 197, 166, 197, 7, 119, 67, 87)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(127, 72, 122, 252, 95, 241, 239, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_right"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 197, 166, 197, 7, 119, 67, 87)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(192, 67, 221, 127, 184, 62, 216, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___boxed(lean_object**);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___boxed(lean_object**);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "andFlattening"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 104, 4, 152, 61, 74, 156, 57)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___f_6_; lean_object* v___f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_6_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_7_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_8_ = lean_st_ref_get(v_a_4_);
v___x_9_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_6_, v___f_7_, v___x_8_, v_e_3_);
lean_dec(v___x_8_);
v___x_10_ = lean_box(v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___boxed(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg(v_e_12_, v_a_13_);
lean_dec(v_a_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_30_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_31_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_32_ = lean_st_ref_get(v_a_17_);
v___x_33_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_30_, v___f_31_, v___x_32_, v_e_16_);
lean_dec(v___x_32_);
v___x_34_ = lean_box(v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___boxed(lean_object* v_e_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(v_e_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(lean_object* v_e_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_56_ = lean_st_ref_take(v_a_52_);
v___x_57_ = lean_box(0);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_54_, v___f_55_, v___x_56_, v_e_51_, v___x_57_);
v___x_59_ = lean_st_ref_put(v_a_52_, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg___boxed(lean_object* v_e_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(v_e_61_, v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(lean_object* v_e_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___f_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_81_ = lean_st_ref_take(v_a_66_);
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_79_, v___f_80_, v___x_81_, v_e_65_, v___x_82_);
v___x_84_ = lean_st_ref_put(v_a_66_, v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___boxed(lean_object* v_e_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(v_e_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
return v_res_100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = l_Lean_Level_ofNat(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3);
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1));
v___x_111_ = l_Lean_mkConst(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_box(0);
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6));
v___x_117_ = l_Lean_mkConst(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_box(0);
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9));
v___x_124_ = l_Lean_mkConst(v___x_123_, v___x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(lean_object* v_lhs_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4);
v___x_134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7);
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10);
v___x_136_ = l_Lean_mkApp3(v___x_133_, v___x_134_, v_lhs_125_, v___x_135_);
v___x_137_ = l_Lean_Meta_Sym_shareCommonInc(v___x_136_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___boxed(lean_object* v_lhs_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_lhs_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
else
{
lean_object* v_key_150_; lean_object* v_tail_151_; size_t v___x_152_; size_t v___x_153_; uint8_t v___x_154_; 
v_key_150_ = lean_ctor_get(v_x_148_, 0);
v_tail_151_ = lean_ctor_get(v_x_148_, 2);
v___x_152_ = lean_ptr_addr(v_key_150_);
v___x_153_ = lean_ptr_addr(v_a_147_);
v___x_154_ = lean_usize_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
v_x_148_ = v_tail_151_;
goto _start;
}
else
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg___boxed(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_156_, v_x_157_);
lean_dec(v_x_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(lean_object* v_m_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_buckets_162_; lean_object* v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v_fold_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_buckets_162_ = lean_ctor_get(v_m_160_, 1);
v___x_163_ = lean_array_get_size(v_buckets_162_);
v___x_164_ = lean_ptr_addr(v_a_161_);
v___x_165_ = ((size_t)3ULL);
v___x_166_ = lean_usize_shift_right(v___x_164_, v___x_165_);
v___x_167_ = lean_usize_to_uint64(v___x_166_);
v___x_168_ = 32ULL;
v___x_169_ = lean_uint64_shift_right(v___x_167_, v___x_168_);
v_fold_170_ = lean_uint64_xor(v___x_167_, v___x_169_);
v___x_171_ = 16ULL;
v___x_172_ = lean_uint64_shift_right(v_fold_170_, v___x_171_);
v___x_173_ = lean_uint64_xor(v_fold_170_, v___x_172_);
v___x_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = lean_usize_of_nat(v___x_163_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_usize_land(v___x_174_, v___x_177_);
v___x_179_ = lean_array_uget_borrowed(v_buckets_162_, v___x_178_);
v___x_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_161_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg___boxed(lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_181_, v_a_182_);
lean_dec_ref(v_a_182_);
lean_dec_ref(v_m_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
return v_x_185_;
}
else
{
lean_object* v_key_187_; lean_object* v_value_188_; lean_object* v_tail_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_215_; 
v_key_187_ = lean_ctor_get(v_x_186_, 0);
v_value_188_ = lean_ctor_get(v_x_186_, 1);
v_tail_189_ = lean_ctor_get(v_x_186_, 2);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_215_ == 0)
{
v___x_191_ = v_x_186_;
v_isShared_192_ = v_isSharedCheck_215_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_tail_189_);
lean_inc(v_value_188_);
lean_inc(v_key_187_);
lean_dec(v_x_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_215_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v_fold_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_193_ = lean_array_get_size(v_x_185_);
v___x_194_ = lean_ptr_addr(v_key_187_);
v___x_195_ = ((size_t)3ULL);
v___x_196_ = lean_usize_shift_right(v___x_194_, v___x_195_);
v___x_197_ = lean_usize_to_uint64(v___x_196_);
v___x_198_ = 32ULL;
v___x_199_ = lean_uint64_shift_right(v___x_197_, v___x_198_);
v_fold_200_ = lean_uint64_xor(v___x_197_, v___x_199_);
v___x_201_ = 16ULL;
v___x_202_ = lean_uint64_shift_right(v_fold_200_, v___x_201_);
v___x_203_ = lean_uint64_xor(v_fold_200_, v___x_202_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = lean_usize_of_nat(v___x_193_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_sub(v___x_205_, v___x_206_);
v___x_208_ = lean_usize_land(v___x_204_, v___x_207_);
v___x_209_ = lean_array_uget_borrowed(v_x_185_, v___x_208_);
lean_inc(v___x_209_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_209_);
v___x_211_ = v___x_191_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_key_187_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_value_188_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___x_209_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_array_uset(v_x_185_, v___x_208_, v___x_211_);
v_x_185_ = v___x_212_;
v_x_186_ = v_tail_189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_216_, lean_object* v_source_217_, lean_object* v_target_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_array_get_size(v_source_217_);
v___x_220_ = lean_nat_dec_lt(v_i_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v_source_217_);
lean_dec(v_i_216_);
return v_target_218_;
}
else
{
lean_object* v_es_221_; lean_object* v___x_222_; lean_object* v_source_223_; lean_object* v_target_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_es_221_ = lean_array_fget(v_source_217_, v_i_216_);
v___x_222_ = lean_box(0);
v_source_223_ = lean_array_fset(v_source_217_, v_i_216_, v___x_222_);
v_target_224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_218_, v_es_221_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_i_216_, v___x_225_);
lean_dec(v_i_216_);
v_i_216_ = v___x_226_;
v_source_217_ = v_source_223_;
v_target_218_ = v_target_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(lean_object* v_data_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_nbuckets_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_229_ = lean_array_get_size(v_data_228_);
v___x_230_ = lean_unsigned_to_nat(2u);
v_nbuckets_231_ = lean_nat_mul(v___x_229_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_box(0);
v___x_234_ = lean_mk_array(v_nbuckets_231_, v___x_233_);
v___x_235_ = lean_array_propagate_mark(v_data_228_, v___x_234_);
v___x_236_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v___x_232_, v_data_228_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(lean_object* v_m_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v_size_240_; lean_object* v_buckets_241_; lean_object* v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v_fold_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v_bkt_258_; uint8_t v___x_259_; 
v_size_240_ = lean_ctor_get(v_m_237_, 0);
v_buckets_241_ = lean_ctor_get(v_m_237_, 1);
v___x_242_ = lean_array_get_size(v_buckets_241_);
v___x_243_ = lean_ptr_addr(v_a_238_);
v___x_244_ = ((size_t)3ULL);
v___x_245_ = lean_usize_shift_right(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_to_uint64(v___x_245_);
v___x_247_ = 32ULL;
v___x_248_ = lean_uint64_shift_right(v___x_246_, v___x_247_);
v_fold_249_ = lean_uint64_xor(v___x_246_, v___x_248_);
v___x_250_ = 16ULL;
v___x_251_ = lean_uint64_shift_right(v_fold_249_, v___x_250_);
v___x_252_ = lean_uint64_xor(v_fold_249_, v___x_251_);
v___x_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = lean_usize_of_nat(v___x_242_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_sub(v___x_254_, v___x_255_);
v___x_257_ = lean_usize_land(v___x_253_, v___x_256_);
v_bkt_258_ = lean_array_uget_borrowed(v_buckets_241_, v___x_257_);
v___x_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_238_, v_bkt_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_buckets_241_);
lean_inc(v_size_240_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_m_237_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; 
v_unused_281_ = lean_ctor_get(v_m_237_, 1);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_m_237_, 0);
lean_dec(v_unused_282_);
v___x_261_ = v_m_237_;
v_isShared_262_ = v_isSharedCheck_280_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_m_237_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_280_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v_size_x27_264_; lean_object* v___x_265_; lean_object* v_buckets_x27_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v_size_x27_264_ = lean_nat_add(v_size_240_, v___x_263_);
lean_dec(v_size_240_);
lean_inc(v_bkt_258_);
v___x_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_265_, 0, v_a_238_);
lean_ctor_set(v___x_265_, 1, v_b_239_);
lean_ctor_set(v___x_265_, 2, v_bkt_258_);
v_buckets_x27_266_ = lean_array_uset(v_buckets_241_, v___x_257_, v___x_265_);
v___x_267_ = lean_unsigned_to_nat(4u);
v___x_268_ = lean_nat_mul(v_size_x27_264_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(3u);
v___x_270_ = lean_nat_div(v___x_268_, v___x_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_array_get_size(v_buckets_x27_266_);
v___x_272_ = lean_nat_dec_le(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v_val_273_; lean_object* v___x_275_; 
v_val_273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_buckets_x27_266_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_val_273_);
lean_ctor_set(v___x_261_, 0, v_size_x27_264_);
v___x_275_ = v___x_261_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_size_x27_264_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_val_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
else
{
lean_object* v___x_278_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_buckets_x27_266_);
lean_ctor_set(v___x_261_, 0, v_size_x27_264_);
v___x_278_ = v___x_261_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_size_x27_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_buckets_x27_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_dec(v_b_239_);
lean_dec_ref(v_a_238_);
return v_m_237_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7));
v___x_301_ = l_Lean_mkConst(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_box(0);
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10));
v___x_312_ = l_Lean_mkConst(v___x_311_, v___x_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(lean_object* v_hyp_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_name_328_; lean_object* v_type_329_; lean_object* v_value_330_; lean_object* v_source_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_406_; 
v_name_328_ = lean_ctor_get(v_hyp_313_, 0);
v_type_329_ = lean_ctor_get(v_hyp_313_, 1);
v_value_330_ = lean_ctor_get(v_hyp_313_, 2);
v_source_331_ = lean_ctor_get(v_hyp_313_, 3);
v_isSharedCheck_406_ = !lean_is_exclusive(v_hyp_313_);
if (v_isSharedCheck_406_ == 0)
{
v___x_333_ = v_hyp_313_;
v_isShared_334_ = v_isSharedCheck_406_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_source_331_);
lean_inc(v_value_330_);
lean_inc(v_type_329_);
lean_inc(v_name_328_);
lean_dec(v_hyp_313_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_406_;
goto v_resetjp_332_;
}
v___jp_322_:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
v___jp_325_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_st_ref_get(v_a_314_);
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v___x_335_, v_type_329_);
lean_dec(v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_337_ = lean_st_ref_take(v_a_314_);
v___x_338_ = lean_box(0);
lean_inc_ref(v_type_329_);
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v___x_337_, v_type_329_, v___x_338_);
v___x_340_ = lean_st_ref_put(v_a_314_, v___x_339_);
v___x_341_ = l_Lean_Expr_cleanupAnnotations(v_type_329_);
v___x_342_ = l_Lean_Expr_isApp(v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v___x_341_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_322_;
}
else
{
lean_object* v_arg_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_arg_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc_ref(v_arg_343_);
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_341_);
v___x_345_ = l_Lean_Expr_isApp(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v___x_344_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_322_;
}
else
{
lean_object* v_arg_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_arg_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc_ref(v_arg_346_);
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_344_);
v___x_348_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v___x_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_322_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_349_, v___x_350_);
lean_dec_ref(v___x_349_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_322_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = l_Lean_Expr_cleanupAnnotations(v_arg_346_);
v___x_353_ = l_Lean_Expr_isApp(v___x_352_);
if (v___x_353_ == 0)
{
lean_dec_ref(v___x_352_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_325_;
}
else
{
lean_object* v_arg_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_arg_354_ = lean_ctor_get(v___x_352_, 1);
lean_inc_ref(v_arg_354_);
v___x_355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_352_);
v___x_356_ = l_Lean_Expr_isApp(v___x_355_);
if (v___x_356_ == 0)
{
lean_dec_ref(v___x_355_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_325_;
}
else
{
lean_object* v_arg_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_arg_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc_ref(v_arg_357_);
v___x_358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_355_);
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1));
v___x_360_ = l_Lean_Expr_isConstOf(v___x_358_, v___x_359_);
lean_dec_ref(v___x_358_);
if (v___x_360_ == 0)
{
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_arg_343_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
goto v___jp_325_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_Expr_cleanupAnnotations(v_arg_343_);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_362_);
lean_dec_ref(v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_354_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_inc_ref(v_arg_357_);
v___x_366_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_357_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8);
lean_inc_ref(v_value_330_);
lean_inc_ref(v_arg_354_);
lean_inc_ref(v_arg_357_);
v___x_369_ = l_Lean_mkApp3(v___x_368_, v_arg_357_, v_arg_354_, v_value_330_);
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v_source_331_);
lean_inc_ref(v___x_370_);
lean_inc(v_name_328_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v___x_370_);
lean_ctor_set(v___x_333_, 2, v___x_369_);
lean_ctor_set(v___x_333_, 1, v_a_367_);
v___x_372_ = v___x_333_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_name_328_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___x_370_);
v___x_372_ = v_reuseFailAlloc_395_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; 
lean_inc_ref(v_arg_354_);
v___x_373_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_354_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11);
v___x_379_ = l_Lean_mkApp3(v___x_378_, v_arg_357_, v_arg_354_, v_value_330_);
v___x_380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_380_, 0, v_name_328_);
lean_ctor_set(v___x_380_, 1, v_a_374_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
lean_ctor_set(v___x_380_, 3, v___x_370_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_372_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_382_);
v___x_384_ = v___x_376_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v___x_372_);
lean_dec_ref_known(v___x_370_, 1);
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_354_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
v_a_387_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_373_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_arg_357_);
lean_dec_ref(v_arg_354_);
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec(v_name_328_);
v_a_396_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_366_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_366_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
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
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_333_);
lean_dec(v_source_331_);
lean_dec_ref(v_value_330_);
lean_dec_ref(v_type_329_);
lean_dec(v_name_328_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object* v_hyp_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(lean_object* v_hyp_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_417_, v_a_419_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(lean_object* v_hyp_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(v_hyp_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(lean_object* v_00_u03b2_449_, lean_object* v_m_450_, lean_object* v_a_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_450_, v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___boxed(lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(v_00_u03b2_453_, v_m_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_m_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1(lean_object* v_00_u03b2_458_, lean_object* v_m_459_, lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v_m_459_, v_a_460_, v_b_461_);
return v___x_462_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(v_00_u03b2_467_, v_a_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec_ref(v_a_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2(lean_object* v_00_u03b2_472_, lean_object* v_data_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_data_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_475_, lean_object* v_i_476_, lean_object* v_source_477_, lean_object* v_target_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v_i_476_, v_source_477_, v_target_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_481_, v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(lean_object* v_worklist_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
if (lean_obj_tag(v_worklist_484_) == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_529_; 
v_head_496_ = lean_ctor_get(v_worklist_484_, 0);
v_tail_497_ = lean_ctor_get(v_worklist_484_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_worklist_484_);
if (v_isSharedCheck_529_ == 0)
{
v___x_499_ = v_worklist_484_;
v_isShared_500_ = v_isSharedCheck_529_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_tail_497_);
lean_inc(v_head_496_);
lean_dec(v_worklist_484_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_529_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; 
lean_inc(v_head_496_);
v___x_501_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_head_496_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
if (lean_obj_tag(v_a_502_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_del_object(v___x_499_);
v___x_503_ = lean_st_ref_take(v_a_485_);
v___x_504_ = lean_array_push(v___x_503_, v_head_496_);
v___x_505_ = lean_st_ref_put(v_a_485_, v___x_504_);
v_worklist_484_ = v_tail_497_;
goto _start;
}
else
{
lean_object* v_val_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_head_496_);
v_val_507_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v_a_502_, 1);
v_fst_508_ = lean_ctor_get(v_val_507_, 0);
v_snd_509_ = lean_ctor_get(v_val_507_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_val_507_);
if (v_isSharedCheck_520_ == 0)
{
v___x_511_ = v_val_507_;
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_inc(v_fst_508_);
lean_dec(v_val_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_snd_509_);
v___x_514_ = v___x_499_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_snd_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_tail_497_);
v___x_514_ = v_reuseFailAlloc_519_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 1);
lean_ctor_set(v___x_511_, 1, v___x_514_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_fst_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_518_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v_worklist_484_ = v___x_516_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_del_object(v___x_499_);
lean_dec(v_tail_497_);
lean_dec(v_head_496_);
v_a_521_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_501_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_501_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object* v_worklist_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec(v_a_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(lean_object* v_worklist_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_541_, v_a_542_, v_a_543_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(lean_object* v_worklist_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(v_worklist_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec(v_a_558_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(lean_object* v_hyp_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; 
lean_inc_ref(v_hyp_573_);
v___x_583_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_573_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_610_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_610_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
if (lean_obj_tag(v_a_584_) == 1)
{
lean_object* v_val_588_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_600_; 
lean_del_object(v___x_586_);
lean_dec_ref(v_hyp_573_);
v_val_588_ = lean_ctor_get(v_a_584_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v_a_584_, 1);
v_fst_589_ = lean_ctor_get(v_val_588_, 0);
v_snd_590_ = lean_ctor_get(v_val_588_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_val_588_);
if (v_isSharedCheck_600_ == 0)
{
v___x_592_ = v_val_588_;
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_inc(v_fst_589_);
lean_dec(v_val_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_600_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 1);
lean_ctor_set(v___x_592_, 1, v___x_594_);
lean_ctor_set(v___x_592_, 0, v_snd_590_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_snd_590_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_599_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v_fst_589_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v___x_597_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v___x_598_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec(v_a_584_);
v___x_601_ = lean_st_ref_take(v_a_574_);
lean_dec(v___x_601_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_603_);
v___x_605_ = lean_array_push(v___x_604_, v_hyp_573_);
v___x_606_ = lean_st_ref_put(v_a_574_, v___x_605_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_602_);
v___x_608_ = v___x_586_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_602_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_hyp_573_);
v_a_611_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_583_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_583_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg___boxed(lean_object* v_hyp_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec(v_a_620_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(lean_object* v_hyp_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_630_, v_a_631_, v_a_632_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___boxed(lean_object* v_hyp_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(v_hyp_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec(v_a_647_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_663_);
v___x_676_ = lean_apply_13(v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, lean_box(0));
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed(lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(lean_object* v_mvarId_692_, lean_object* v_x_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
v___f_707_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_707_, 0, v_x_693_);
lean_closure_set(v___f_707_, 1, v___y_694_);
lean_closure_set(v___f_707_, 2, v___y_695_);
lean_closure_set(v___f_707_, 3, v___y_696_);
lean_closure_set(v___f_707_, 4, v___y_697_);
lean_closure_set(v___f_707_, 5, v___y_698_);
lean_closure_set(v___f_707_, 6, v___y_699_);
lean_closure_set(v___f_707_, 7, v___y_700_);
lean_closure_set(v___f_707_, 8, v___y_701_);
v___x_708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_692_, v___f_707_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
return v___x_708_;
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___boxed(lean_object* v_mvarId_717_, lean_object* v_x_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_717_, v_x_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(lean_object* v_00_u03b1_733_, lean_object* v_mvarId_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___boxed(lean_object* v_00_u03b1_750_, lean_object* v_mvarId_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(v_00_u03b1_750_, v_mvarId_751_, v_x_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(uint8_t v_isZero_767_, lean_object* v_val_768_, lean_object* v_____r_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_caches_784_; lean_object* v_typeAnalysis_785_; lean_object* v_target_786_; lean_object* v_hypotheses_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v___x_783_ = lean_st_ref_take(v___y_772_);
v_caches_784_ = lean_ctor_get(v___x_783_, 0);
v_typeAnalysis_785_ = lean_ctor_get(v___x_783_, 1);
v_target_786_ = lean_ctor_get(v___x_783_, 2);
v_hypotheses_787_ = lean_ctor_get(v___x_783_, 3);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v___x_783_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_hypotheses_787_);
lean_inc(v_target_786_);
lean_inc(v_typeAnalysis_785_);
lean_inc(v_caches_784_);
lean_dec(v___x_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
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
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_caches_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_typeAnalysis_785_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_target_786_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_hypotheses_787_);
v___x_792_ = v_reuseFailAlloc_795_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*4, v_isZero_767_);
v___x_793_ = lean_st_ref_put(v___y_772_, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v_val_768_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0___boxed(lean_object* v_isZero_797_, lean_object* v_val_798_, lean_object* v_____r_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_isZero_boxed_813_; lean_object* v_res_814_; 
v_isZero_boxed_813_ = lean_unbox(v_isZero_797_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_boxed_813_, v_val_798_, v_____r_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(lean_object* v_msgData_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v_env_822_; uint8_t v___x_823_; lean_object* v_env_824_; lean_object* v___x_825_; lean_object* v_toCold_826_; lean_object* v_mctx_827_; lean_object* v_lctx_828_; lean_object* v_options_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_821_ = lean_st_ref_get(v___y_819_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = 0;
v_env_824_ = l_Lean_Environment_setRecordingDeps(v_env_822_, v___x_823_);
v___x_825_ = lean_st_ref_get(v___y_817_);
v_toCold_826_ = lean_ctor_get(v___y_818_, 0);
v_mctx_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc_ref(v_mctx_827_);
lean_dec(v___x_825_);
v_lctx_828_ = lean_ctor_get(v___y_816_, 2);
v_options_829_ = lean_ctor_get(v_toCold_826_, 2);
lean_inc_ref(v_options_829_);
lean_inc_ref(v_lctx_828_);
v___x_830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_830_, 0, v_env_824_);
lean_ctor_set(v___x_830_, 1, v_mctx_827_);
lean_ctor_set(v___x_830_, 2, v_lctx_828_);
lean_ctor_set(v___x_830_, 3, v_options_829_);
v___x_831_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_msgData_815_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0___boxed(lean_object* v_msgData_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msgData_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_839_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_840_; double v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_float_of_nat(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(lean_object* v_cls_845_, lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_ref_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_899_; 
v_ref_852_ = lean_ctor_get(v___y_849_, 2);
v___x_853_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msg_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_899_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_899_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v_traceState_859_; lean_object* v_env_860_; lean_object* v_nextMacroScope_861_; lean_object* v_ngen_862_; lean_object* v_auxDeclNGen_863_; lean_object* v_cache_864_; lean_object* v_recordedDeps_865_; lean_object* v_messages_866_; lean_object* v_infoState_867_; lean_object* v_snapshotTasks_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_898_; 
v___x_858_ = lean_st_ref_take(v___y_850_);
v_traceState_859_ = lean_ctor_get(v___x_858_, 4);
v_env_860_ = lean_ctor_get(v___x_858_, 0);
v_nextMacroScope_861_ = lean_ctor_get(v___x_858_, 1);
v_ngen_862_ = lean_ctor_get(v___x_858_, 2);
v_auxDeclNGen_863_ = lean_ctor_get(v___x_858_, 3);
v_cache_864_ = lean_ctor_get(v___x_858_, 5);
v_recordedDeps_865_ = lean_ctor_get(v___x_858_, 6);
v_messages_866_ = lean_ctor_get(v___x_858_, 7);
v_infoState_867_ = lean_ctor_get(v___x_858_, 8);
v_snapshotTasks_868_ = lean_ctor_get(v___x_858_, 9);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_898_ == 0)
{
v___x_870_ = v___x_858_;
v_isShared_871_ = v_isSharedCheck_898_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_snapshotTasks_868_);
lean_inc(v_infoState_867_);
lean_inc(v_messages_866_);
lean_inc(v_recordedDeps_865_);
lean_inc(v_cache_864_);
lean_inc(v_traceState_859_);
lean_inc(v_auxDeclNGen_863_);
lean_inc(v_ngen_862_);
lean_inc(v_nextMacroScope_861_);
lean_inc(v_env_860_);
lean_dec(v___x_858_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_898_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint64_t v_tid_872_; lean_object* v_traces_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_897_; 
v_tid_872_ = lean_ctor_get_uint64(v_traceState_859_, sizeof(void*)*1);
v_traces_873_ = lean_ctor_get(v_traceState_859_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_traceState_859_);
if (v_isSharedCheck_897_ == 0)
{
v___x_875_ = v_traceState_859_;
v_isShared_876_ = v_isSharedCheck_897_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_traces_873_);
lean_dec(v_traceState_859_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_897_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; double v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_877_ = lean_box(0);
v___x_878_ = lean_box(0);
v___x_879_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0);
v___x_880_ = 0;
v___x_881_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1));
v___x_882_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_882_, 0, v_cls_845_);
lean_ctor_set(v___x_882_, 1, v___x_878_);
lean_ctor_set(v___x_882_, 2, v___x_881_);
lean_ctor_set_float(v___x_882_, sizeof(void*)*3, v___x_879_);
lean_ctor_set_float(v___x_882_, sizeof(void*)*3 + 8, v___x_879_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*3 + 16, v___x_880_);
v___x_883_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2));
v___x_884_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v_a_854_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_inc(v_ref_852_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_ref_852_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_PersistentArray_push___redArg(v_traces_873_, v___x_885_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_886_);
v___x_888_ = v___x_875_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_886_);
lean_ctor_set_uint64(v_reuseFailAlloc_896_, sizeof(void*)*1, v_tid_872_);
v___x_888_ = v_reuseFailAlloc_896_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 4, v___x_888_);
v___x_890_ = v___x_870_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_env_860_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_nextMacroScope_861_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_ngen_862_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_auxDeclNGen_863_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_cache_864_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_recordedDeps_865_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_messages_866_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_infoState_867_);
lean_ctor_set(v_reuseFailAlloc_895_, 9, v_snapshotTasks_868_);
v___x_890_ = v_reuseFailAlloc_895_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_st_ref_put(v___y_850_, v___x_890_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_877_);
v___x_893_ = v___x_856_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_877_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___boxed(lean_object* v_cls_900_, lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_900_, v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5(void){
_start:
{
lean_object* v_cls_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_cls_917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4));
v___x_919_ = l_Lean_Name_append(v___x_918_, v_cls_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(lean_object* v_a_923_, lean_object* v_as_924_, size_t v_i_925_, size_t v_stop_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_a_942_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_eq(v_i_925_, v_stop_926_);
if (v___x_948_ == 0)
{
lean_object* v_toCold_949_; lean_object* v_options_950_; uint8_t v_hasTrace_951_; 
v_toCold_949_ = lean_ctor_get(v___y_938_, 0);
v_options_950_ = lean_ctor_get(v_toCold_949_, 2);
v_hasTrace_951_ = lean_ctor_get_uint8(v_options_950_, sizeof(void*)*1);
if (v_hasTrace_951_ == 0)
{
goto v___jp_946_;
}
else
{
lean_object* v_inheritedTraceOptions_952_; lean_object* v_cls_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v_inheritedTraceOptions_952_ = lean_ctor_get(v_toCold_949_, 11);
v_cls_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_952_, v_options_950_, v___x_954_);
if (v___x_955_ == 0)
{
goto v___jp_946_;
}
else
{
lean_object* v_type_956_; lean_object* v___x_957_; lean_object* v_type_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_type_956_ = lean_ctor_get(v_a_923_, 1);
v___x_957_ = lean_array_uget_borrowed(v_as_924_, v_i_925_);
v_type_958_ = lean_ctor_get(v___x_957_, 1);
lean_inc_ref(v_type_956_);
v___x_959_ = l_Lean_MessageData_ofExpr(v_type_956_);
v___x_960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
lean_inc_ref(v_type_958_);
v___x_962_ = l_Lean_MessageData_ofExpr(v_type_958_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_953_, v___x_963_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v_a_942_ = v_a_965_;
goto v___jp_941_;
}
else
{
lean_dec_ref(v_a_923_);
return v___x_964_;
}
}
}
}
else
{
lean_object* v___x_966_; 
lean_dec_ref(v_a_923_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v_b_927_);
return v___x_966_;
}
v___jp_941_:
{
size_t v___x_943_; size_t v___x_944_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_925_, v___x_943_);
v_i_925_ = v___x_944_;
v_b_927_ = v_a_942_;
goto _start;
}
v___jp_946_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_box(0);
v_a_942_ = v___x_947_;
goto v___jp_941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___boxed(lean_object** _args){
lean_object* v_a_967_ = _args[0];
lean_object* v_as_968_ = _args[1];
lean_object* v_i_969_ = _args[2];
lean_object* v_stop_970_ = _args[3];
lean_object* v_b_971_ = _args[4];
lean_object* v___y_972_ = _args[5];
lean_object* v___y_973_ = _args[6];
lean_object* v___y_974_ = _args[7];
lean_object* v___y_975_ = _args[8];
lean_object* v___y_976_ = _args[9];
lean_object* v___y_977_ = _args[10];
lean_object* v___y_978_ = _args[11];
lean_object* v___y_979_ = _args[12];
lean_object* v___y_980_ = _args[13];
lean_object* v___y_981_ = _args[14];
lean_object* v___y_982_ = _args[15];
lean_object* v___y_983_ = _args[16];
lean_object* v___y_984_ = _args[17];
_start:
{
size_t v_i_boxed_985_; size_t v_stop_boxed_986_; lean_object* v_res_987_; 
v_i_boxed_985_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_986_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v_a_967_, v_as_968_, v_i_boxed_985_, v_stop_boxed_986_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v_as_968_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(lean_object* v_as_990_, size_t v_i_991_, size_t v_stop_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_a_1008_; lean_object* v___y_1014_; uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_eq(v_i_991_, v_stop_992_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1017_ = lean_array_uget_borrowed(v_as_990_, v_i_991_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
v___x_1020_ = lean_st_mk_ref(v___x_1019_);
lean_inc(v___x_1017_);
v___x_1021_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v___x_1017_, v___x_1020_, v___y_994_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v_isZero_1024_; 
lean_dec_ref_known(v___x_1021_, 1);
v___x_1022_ = lean_st_ref_get(v___x_1020_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_array_get_size(v___x_1022_);
v_isZero_1024_ = lean_nat_dec_eq(v___x_1023_, v___x_1018_);
if (v_isZero_1024_ == 1)
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v___x_1018_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v_caches_1027_; lean_object* v_typeAnalysis_1028_; lean_object* v_target_1029_; lean_object* v_hypotheses_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v___x_1026_ = lean_st_ref_take(v___y_996_);
v_caches_1027_ = lean_ctor_get(v___x_1026_, 0);
v_typeAnalysis_1028_ = lean_ctor_get(v___x_1026_, 1);
v_target_1029_ = lean_ctor_get(v___x_1026_, 2);
v_hypotheses_1030_ = lean_ctor_get(v___x_1026_, 3);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v___x_1026_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_hypotheses_1030_);
lean_inc(v_target_1029_);
lean_inc(v_typeAnalysis_1028_);
lean_inc(v_caches_1027_);
lean_dec(v___x_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_caches_1027_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_typeAnalysis_1028_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_target_1029_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_hypotheses_1030_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*4, v_isZero_1024_);
v___x_1036_ = lean_st_ref_put(v___y_996_, v___x_1035_);
v_a_1008_ = v___x_1022_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1023_);
lean_inc(v___x_1017_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1017_, v___x_1022_, v___x_1040_, v___x_1041_, v___x_1039_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; lean_object* v_caches_1044_; lean_object* v_typeAnalysis_1045_; lean_object* v_target_1046_; lean_object* v_hypotheses_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref_known(v___x_1042_, 1);
v___x_1043_ = lean_st_ref_take(v___y_996_);
v_caches_1044_ = lean_ctor_get(v___x_1043_, 0);
v_typeAnalysis_1045_ = lean_ctor_get(v___x_1043_, 1);
v_target_1046_ = lean_ctor_get(v___x_1043_, 2);
v_hypotheses_1047_ = lean_ctor_get(v___x_1043_, 3);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1043_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_hypotheses_1047_);
lean_inc(v_target_1046_);
lean_inc(v_typeAnalysis_1045_);
lean_inc(v_caches_1044_);
lean_dec(v___x_1043_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_caches_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_typeAnalysis_1045_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_target_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_hypotheses_1047_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; 
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*4, v___x_1025_);
v___x_1053_ = lean_st_ref_put(v___y_996_, v___x_1052_);
v_a_1008_ = v___x_1022_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v___x_1022_);
lean_dec_ref(v_b_993_);
v_a_1056_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1042_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1042_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v_one_1064_; lean_object* v_n_1065_; uint8_t v_isZero_1066_; 
v_one_1064_ = lean_unsigned_to_nat(1u);
v_n_1065_ = lean_nat_sub(v___x_1023_, v_one_1064_);
v_isZero_1066_ = lean_nat_dec_eq(v_n_1065_, v___x_1018_);
lean_dec(v_n_1065_);
if (v_isZero_1066_ == 1)
{
lean_object* v_newHyp_1067_; lean_object* v_type_1068_; lean_object* v_type_1069_; uint8_t v___x_1070_; 
v_newHyp_1067_ = lean_array_fget_borrowed(v___x_1022_, v___x_1018_);
v_type_1068_ = lean_ctor_get(v_newHyp_1067_, 1);
v_type_1069_ = lean_ctor_get(v___x_1017_, 1);
v___x_1070_ = lean_expr_eqv(v_type_1068_, v_type_1069_);
if (v___x_1070_ == 0)
{
lean_object* v_toCold_1071_; lean_object* v_options_1072_; lean_object* v_inheritedTraceOptions_1073_; uint8_t v_hasTrace_1074_; 
v_toCold_1071_ = lean_ctor_get(v___y_1004_, 0);
v_options_1072_ = lean_ctor_get(v_toCold_1071_, 2);
v_inheritedTraceOptions_1073_ = lean_ctor_get(v_toCold_1071_, 11);
v_hasTrace_1074_ = lean_ctor_get_uint8(v_options_1072_, sizeof(void*)*1);
if (v_hasTrace_1074_ == 0)
{
goto v___jp_1075_;
}
else
{
lean_object* v_cls_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_cls_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_1079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_1080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1073_, v_options_1072_, v___x_1079_);
if (v___x_1080_ == 0)
{
goto v___jp_1075_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc_ref(v_type_1069_);
v___x_1081_ = l_Lean_MessageData_ofExpr(v_type_1069_);
v___x_1082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_inc_ref(v_type_1068_);
v___x_1084_ = l_Lean_MessageData_ofExpr(v_type_1068_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1078_, v___x_1085_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_1066_, v___x_1022_, v_a_1087_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
v___y_1014_ = v___x_1088_;
goto v___jp_1013_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v___x_1022_);
lean_dec_ref(v_b_993_);
v_a_1089_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1086_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1086_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
v___jp_1075_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_1066_, v___x_1022_, v___x_1076_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
v___y_1014_ = v___x_1077_;
goto v___jp_1013_;
}
}
else
{
v_a_1008_ = v___x_1022_;
goto v___jp_1007_;
}
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_lt(v___x_1018_, v___x_1023_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v_caches_1099_; lean_object* v_typeAnalysis_1100_; lean_object* v_target_1101_; lean_object* v_hypotheses_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1111_; 
v___x_1098_ = lean_st_ref_take(v___y_996_);
v_caches_1099_ = lean_ctor_get(v___x_1098_, 0);
v_typeAnalysis_1100_ = lean_ctor_get(v___x_1098_, 1);
v_target_1101_ = lean_ctor_get(v___x_1098_, 2);
v_hypotheses_1102_ = lean_ctor_get(v___x_1098_, 3);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_hypotheses_1102_);
lean_inc(v_target_1101_);
lean_inc(v_typeAnalysis_1100_);
lean_inc(v_caches_1099_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
uint8_t v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = 1;
if (v_isShared_1105_ == 0)
{
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_caches_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_typeAnalysis_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_target_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_hypotheses_1102_);
v___x_1108_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*4, v___x_1106_);
v___x_1109_ = lean_st_ref_put(v___y_996_, v___x_1108_);
v_a_1008_ = v___x_1022_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1023_);
lean_inc(v___x_1017_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1017_, v___x_1022_, v___x_1113_, v___x_1114_, v___x_1112_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v_caches_1117_; lean_object* v_typeAnalysis_1118_; lean_object* v_target_1119_; lean_object* v_hypotheses_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref_known(v___x_1115_, 1);
v___x_1116_ = lean_st_ref_take(v___y_996_);
v_caches_1117_ = lean_ctor_get(v___x_1116_, 0);
v_typeAnalysis_1118_ = lean_ctor_get(v___x_1116_, 1);
v_target_1119_ = lean_ctor_get(v___x_1116_, 2);
v_hypotheses_1120_ = lean_ctor_get(v___x_1116_, 3);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1116_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_hypotheses_1120_);
lean_inc(v_target_1119_);
lean_inc(v_typeAnalysis_1118_);
lean_inc(v_caches_1117_);
lean_dec(v___x_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_caches_1117_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_typeAnalysis_1118_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_target_1119_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_hypotheses_1120_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; 
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*4, v___x_1097_);
v___x_1126_ = lean_st_ref_put(v___y_996_, v___x_1125_);
v_a_1008_ = v___x_1022_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v___x_1022_);
lean_dec_ref(v_b_993_);
v_a_1129_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1115_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1115_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v___x_1020_);
lean_dec_ref(v_b_993_);
v_a_1137_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1021_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1021_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_b_993_);
return v___x_1145_;
}
v___jp_1007_:
{
lean_object* v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; 
v___x_1009_ = l_Array_append___redArg(v_b_993_, v_a_1008_);
lean_dec_ref(v_a_1008_);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_991_, v___x_1010_);
v_i_991_ = v___x_1011_;
v_b_993_ = v___x_1009_;
goto _start;
}
v___jp_1013_:
{
if (lean_obj_tag(v___y_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___y_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___y_1014_, 1);
v_a_1008_ = v_a_1015_;
goto v___jp_1007_;
}
else
{
lean_dec_ref(v_b_993_);
return v___y_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___boxed(lean_object** _args){
lean_object* v_as_1146_ = _args[0];
lean_object* v_i_1147_ = _args[1];
lean_object* v_stop_1148_ = _args[2];
lean_object* v_b_1149_ = _args[3];
lean_object* v___y_1150_ = _args[4];
lean_object* v___y_1151_ = _args[5];
lean_object* v___y_1152_ = _args[6];
lean_object* v___y_1153_ = _args[7];
lean_object* v___y_1154_ = _args[8];
lean_object* v___y_1155_ = _args[9];
lean_object* v___y_1156_ = _args[10];
lean_object* v___y_1157_ = _args[11];
lean_object* v___y_1158_ = _args[12];
lean_object* v___y_1159_ = _args[13];
lean_object* v___y_1160_ = _args[14];
lean_object* v___y_1161_ = _args[15];
lean_object* v___y_1162_ = _args[16];
_start:
{
size_t v_i_boxed_1163_; size_t v_stop_boxed_1164_; lean_object* v_res_1165_; 
v_i_boxed_1163_ = lean_unbox_usize(v_i_1147_);
lean_dec(v_i_1147_);
v_stop_boxed_1164_ = lean_unbox_usize(v_stop_1148_);
lean_dec(v_stop_1148_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_as_1146_, v_i_boxed_1163_, v_stop_boxed_1164_, v_b_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v_as_1146_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_hypotheses_1182_; lean_object* v___x_1183_; lean_object* v_caches_1184_; lean_object* v_typeAnalysis_1185_; lean_object* v_target_1186_; uint8_t v_didChange_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1250_; 
v___x_1181_ = lean_st_ref_get(v___y_1170_);
v_hypotheses_1182_ = lean_ctor_get(v___x_1181_, 3);
lean_inc_ref(v_hypotheses_1182_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_st_ref_take(v___y_1170_);
v_caches_1184_ = lean_ctor_get(v___x_1183_, 0);
v_typeAnalysis_1185_ = lean_ctor_get(v___x_1183_, 1);
v_target_1186_ = lean_ctor_get(v___x_1183_, 2);
v_didChange_1187_ = lean_ctor_get_uint8(v___x_1183_, sizeof(void*)*4);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1183_, 3);
lean_dec(v_unused_1251_);
v___x_1189_ = v___x_1183_;
v_isShared_1190_ = v_isSharedCheck_1250_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_target_1186_);
lean_inc(v_typeAnalysis_1185_);
lean_inc(v_caches_1184_);
lean_dec(v___x_1183_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1250_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 3, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_caches_1184_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_typeAnalysis_1185_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_target_1186_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v___x_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*4, v_didChange_1187_);
v___x_1194_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1195_ = lean_st_ref_put(v___y_1170_, v___x_1194_);
v___x_1196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___closed__0));
v___x_1197_ = lean_array_get_size(v_hypotheses_1182_);
v___x_1198_ = lean_nat_dec_lt(v___x_1191_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v_caches_1200_; lean_object* v_typeAnalysis_1201_; lean_object* v_target_1202_; uint8_t v_didChange_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_hypotheses_1182_);
v___x_1199_ = lean_st_ref_take(v___y_1170_);
v_caches_1200_ = lean_ctor_get(v___x_1199_, 0);
v_typeAnalysis_1201_ = lean_ctor_get(v___x_1199_, 1);
v_target_1202_ = lean_ctor_get(v___x_1199_, 2);
v_didChange_1203_ = lean_ctor_get_uint8(v___x_1199_, sizeof(void*)*4);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1199_, 3);
lean_dec(v_unused_1214_);
v___x_1205_ = v___x_1199_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_target_1202_);
lean_inc(v_typeAnalysis_1201_);
lean_inc(v_caches_1200_);
lean_dec(v___x_1199_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_box(0);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 3, v___x_1196_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_caches_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_typeAnalysis_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_target_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*4, v_didChange_1203_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_put(v___y_1170_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1207_);
return v___x_1211_;
}
}
}
else
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = lean_usize_of_nat(v___x_1197_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_hypotheses_1182_, v___x_1215_, v___x_1216_, v___x_1196_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec_ref(v_hypotheses_1182_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1240_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1240_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1240_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v_caches_1223_; lean_object* v_typeAnalysis_1224_; lean_object* v_target_1225_; uint8_t v_didChange_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
v___x_1222_ = lean_st_ref_take(v___y_1170_);
v_caches_1223_ = lean_ctor_get(v___x_1222_, 0);
v_typeAnalysis_1224_ = lean_ctor_get(v___x_1222_, 1);
v_target_1225_ = lean_ctor_get(v___x_1222_, 2);
v_didChange_1226_ = lean_ctor_get_uint8(v___x_1222_, sizeof(void*)*4);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1222_, 3);
lean_dec(v_unused_1239_);
v___x_1228_ = v___x_1222_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_target_1225_);
lean_inc(v_typeAnalysis_1224_);
lean_inc(v_caches_1223_);
lean_dec(v___x_1222_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v_a_1218_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_caches_1223_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_typeAnalysis_1224_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_target_1225_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_a_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*4, v_didChange_1226_);
v___x_1232_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = lean_st_ref_put(v___y_1170_, v___x_1232_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1230_);
v___x_1235_ = v___x_1220_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1217_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1217_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed(lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(lean_object* v_g_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___f_1281_; lean_object* v___x_1282_; 
v___f_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0));
v___x_1282_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_g_1267_, v___f_1281_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___boxed(lean_object* v_g_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v_g_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(lean_object* v_cls_1298_, lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1298_, v_msg_1299_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___boxed(lean_object* v_cls_1314_, lean_object* v_msg_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(v_cls_1314_, v_msg_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_unsigned_to_nat(16u);
v___x_1332_ = lean_mk_array(v___x_1331_, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v_target_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1348_ = lean_st_ref_get(v___y_1337_);
v_target_1349_ = lean_ctor_get(v___x_1348_, 2);
lean_inc_ref(v_target_1349_);
lean_dec(v___x_1348_);
v___x_1350_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1349_);
lean_dec_ref(v_target_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1);
v___x_1352_ = lean_st_mk_ref(v___x_1351_);
v___x_1353_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v___x_1350_, v___x_1352_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1363_; 
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v___x_1353_, 0);
lean_dec(v_unused_1364_);
v___x_1355_ = v___x_1353_;
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v___x_1353_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1357_ = lean_st_ref_get(v___x_1352_);
lean_dec(v___x_1352_);
lean_dec(v___x_1357_);
v___x_1358_ = 0;
v___x_1359_ = lean_box(v___x_1358_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v___x_1352_);
v_a_1365_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1353_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1353_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1385_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
}
#ifdef __cplusplus
}
#endif
