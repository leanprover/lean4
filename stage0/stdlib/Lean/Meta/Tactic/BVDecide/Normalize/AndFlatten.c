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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___boxed, .m_arity = 11, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_6_; lean_object* v___f_7_; lean_object* v___f_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_6_ = lean_st_ref_get(v_a_4_);
v___f_7_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_8_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_9_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_7_, v___f_8_, v___x_6_, v_e_3_);
lean_dec(v___x_6_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___f_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_27_ = lean_st_ref_get(v_a_17_);
v___f_28_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_29_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_30_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_28_, v___f_29_, v___x_27_, v_e_16_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___boxed(lean_object* v_e_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(v_e_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(lean_object* v_e_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_48_ = lean_st_ref_take(v_a_46_);
v___f_49_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_51_ = lean_box(0);
v___x_52_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_49_, v___f_50_, v___x_48_, v_e_45_, v___x_51_);
v___x_53_ = lean_st_ref_set(v_a_46_, v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg___boxed(lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___redArg(v_e_55_, v_a_56_);
lean_dec(v_a_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(lean_object* v_e_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_st_ref_take(v_a_60_);
v___f_71_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_73_ = lean_box(0);
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_71_, v___f_72_, v___x_70_, v_e_59_, v___x_73_);
v___x_75_ = lean_st_ref_set(v_a_60_, v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache___boxed(lean_object* v_e_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_cache(v_e_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
return v_res_88_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = l_Lean_Level_ofNat(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__2);
v___x_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__3);
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1));
v___x_99_ = l_Lean_mkConst(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__6));
v___x_105_ = l_Lean_mkConst(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_box(0);
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9));
v___x_112_ = l_Lean_mkConst(v___x_111_, v___x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(lean_object* v_lhs_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__4);
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__7);
v___x_123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__10);
v___x_124_ = l_Lean_mkApp3(v___x_121_, v___x_122_, v_lhs_113_, v___x_123_);
v___x_125_ = l_Lean_Meta_Sym_shareCommonInc(v___x_124_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___boxed(lean_object* v_lhs_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_lhs_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_134_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(lean_object* v_a_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
else
{
lean_object* v_key_138_; lean_object* v_tail_139_; size_t v___x_140_; size_t v___x_141_; uint8_t v___x_142_; 
v_key_138_ = lean_ctor_get(v_x_136_, 0);
v_tail_139_ = lean_ctor_get(v_x_136_, 2);
v___x_140_ = lean_ptr_addr(v_key_138_);
v___x_141_ = lean_ptr_addr(v_a_135_);
v___x_142_ = lean_usize_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
v_x_136_ = v_tail_139_;
goto _start;
}
else
{
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg___boxed(lean_object* v_a_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_144_, v_x_145_);
lean_dec(v_x_145_);
lean_dec_ref(v_a_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(lean_object* v_m_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_buckets_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_buckets_150_ = lean_ctor_get(v_m_148_, 1);
v___x_151_ = lean_array_get_size(v_buckets_150_);
v___x_152_ = lean_ptr_addr(v_a_149_);
v___x_153_ = ((size_t)3ULL);
v___x_154_ = lean_usize_shift_right(v___x_152_, v___x_153_);
v___x_155_ = lean_usize_to_uint64(v___x_154_);
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___x_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___x_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_151_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v___x_167_ = lean_array_uget_borrowed(v_buckets_150_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_149_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg___boxed(lean_object* v_m_169_, lean_object* v_a_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_169_, v_a_170_);
lean_dec_ref(v_a_170_);
lean_dec_ref(v_m_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
return v_x_173_;
}
else
{
lean_object* v_key_175_; lean_object* v_value_176_; lean_object* v_tail_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_203_; 
v_key_175_ = lean_ctor_get(v_x_174_, 0);
v_value_176_ = lean_ctor_get(v_x_174_, 1);
v_tail_177_ = lean_ctor_get(v_x_174_, 2);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_203_ == 0)
{
v___x_179_ = v_x_174_;
v_isShared_180_ = v_isSharedCheck_203_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_tail_177_);
lean_inc(v_value_176_);
lean_inc(v_key_175_);
lean_dec(v_x_174_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_203_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v_fold_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_181_ = lean_array_get_size(v_x_173_);
v___x_182_ = lean_ptr_addr(v_key_175_);
v___x_183_ = ((size_t)3ULL);
v___x_184_ = lean_usize_shift_right(v___x_182_, v___x_183_);
v___x_185_ = lean_usize_to_uint64(v___x_184_);
v___x_186_ = 32ULL;
v___x_187_ = lean_uint64_shift_right(v___x_185_, v___x_186_);
v_fold_188_ = lean_uint64_xor(v___x_185_, v___x_187_);
v___x_189_ = 16ULL;
v___x_190_ = lean_uint64_shift_right(v_fold_188_, v___x_189_);
v___x_191_ = lean_uint64_xor(v_fold_188_, v___x_190_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = lean_usize_of_nat(v___x_181_);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v___x_193_, v___x_194_);
v___x_196_ = lean_usize_land(v___x_192_, v___x_195_);
v___x_197_ = lean_array_uget_borrowed(v_x_173_, v___x_196_);
lean_inc(v___x_197_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 2, v___x_197_);
v___x_199_ = v___x_179_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_key_175_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_value_176_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v___x_197_);
v___x_199_ = v_reuseFailAlloc_202_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_uset(v_x_173_, v___x_196_, v___x_199_);
v_x_173_ = v___x_200_;
v_x_174_ = v_tail_177_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(lean_object* v_i_204_, lean_object* v_source_205_, lean_object* v_target_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_array_get_size(v_source_205_);
v___x_208_ = lean_nat_dec_lt(v_i_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v_source_205_);
lean_dec(v_i_204_);
return v_target_206_;
}
else
{
lean_object* v_es_209_; lean_object* v___x_210_; lean_object* v_source_211_; lean_object* v_target_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_es_209_ = lean_array_fget(v_source_205_, v_i_204_);
v___x_210_ = lean_box(0);
v_source_211_ = lean_array_fset(v_source_205_, v_i_204_, v___x_210_);
v_target_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_206_, v_es_209_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_i_204_, v___x_213_);
lean_dec(v_i_204_);
v_i_204_ = v___x_214_;
v_source_205_ = v_source_211_;
v_target_206_ = v_target_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(lean_object* v_data_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_nbuckets_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_217_ = lean_array_get_size(v_data_216_);
v___x_218_ = lean_unsigned_to_nat(2u);
v_nbuckets_219_ = lean_nat_mul(v___x_217_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_box(0);
v___x_222_ = lean_mk_array(v_nbuckets_219_, v___x_221_);
v___x_223_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v___x_220_, v_data_216_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(lean_object* v_m_224_, lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v_size_227_; lean_object* v_buckets_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v_bkt_245_; uint8_t v___x_246_; 
v_size_227_ = lean_ctor_get(v_m_224_, 0);
v_buckets_228_ = lean_ctor_get(v_m_224_, 1);
v___x_229_ = lean_array_get_size(v_buckets_228_);
v___x_230_ = lean_ptr_addr(v_a_225_);
v___x_231_ = ((size_t)3ULL);
v___x_232_ = lean_usize_shift_right(v___x_230_, v___x_231_);
v___x_233_ = lean_usize_to_uint64(v___x_232_);
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___x_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___x_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_229_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v_bkt_245_ = lean_array_uget_borrowed(v_buckets_228_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_225_, v_bkt_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_267_; 
lean_inc_ref(v_buckets_228_);
lean_inc(v_size_227_);
v_isSharedCheck_267_ = !lean_is_exclusive(v_m_224_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; lean_object* v_unused_269_; 
v_unused_268_ = lean_ctor_get(v_m_224_, 1);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_m_224_, 0);
lean_dec(v_unused_269_);
v___x_248_ = v_m_224_;
v_isShared_249_ = v_isSharedCheck_267_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_m_224_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_267_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v_size_x27_251_; lean_object* v___x_252_; lean_object* v_buckets_x27_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v_size_x27_251_ = lean_nat_add(v_size_227_, v___x_250_);
lean_dec(v_size_227_);
lean_inc(v_bkt_245_);
v___x_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_252_, 0, v_a_225_);
lean_ctor_set(v___x_252_, 1, v_b_226_);
lean_ctor_set(v___x_252_, 2, v_bkt_245_);
v_buckets_x27_253_ = lean_array_uset(v_buckets_228_, v___x_244_, v___x_252_);
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_nat_mul(v_size_x27_251_, v___x_254_);
v___x_256_ = lean_unsigned_to_nat(3u);
v___x_257_ = lean_nat_div(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_array_get_size(v_buckets_x27_253_);
v___x_259_ = lean_nat_dec_le(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v_val_260_; lean_object* v___x_262_; 
v_val_260_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_buckets_x27_253_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_val_260_);
lean_ctor_set(v___x_248_, 0, v_size_x27_251_);
v___x_262_ = v___x_248_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_size_x27_251_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_val_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v___x_265_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_buckets_x27_253_);
lean_ctor_set(v___x_248_, 0, v_size_x27_251_);
v___x_265_ = v___x_248_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_size_x27_251_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_buckets_x27_253_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_dec(v_b_226_);
lean_dec_ref(v_a_225_);
return v_m_224_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7));
v___x_288_ = l_Lean_mkConst(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10));
v___x_299_ = l_Lean_mkConst(v___x_298_, v___x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(lean_object* v_hyp_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_312_; lean_object* v_name_313_; lean_object* v_type_314_; lean_object* v_value_315_; lean_object* v_source_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_393_; 
v___x_312_ = lean_st_ref_get(v_a_301_);
v_name_313_ = lean_ctor_get(v_hyp_300_, 0);
v_type_314_ = lean_ctor_get(v_hyp_300_, 1);
v_value_315_ = lean_ctor_get(v_hyp_300_, 2);
v_source_316_ = lean_ctor_get(v_hyp_300_, 3);
v_isSharedCheck_393_ = !lean_is_exclusive(v_hyp_300_);
if (v_isSharedCheck_393_ == 0)
{
v___x_318_ = v_hyp_300_;
v_isShared_319_ = v_isSharedCheck_393_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_source_316_);
lean_inc(v_value_315_);
lean_inc(v_type_314_);
lean_inc(v_name_313_);
lean_dec(v_hyp_300_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_393_;
goto v_resetjp_317_;
}
v___jp_309_:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v___x_312_, v_type_314_);
lean_dec(v___x_312_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_321_ = lean_st_ref_take(v_a_301_);
v___x_322_ = lean_box(0);
lean_inc_ref(v_type_314_);
v___x_323_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v___x_321_, v_type_314_, v___x_322_);
v___x_324_ = lean_st_ref_set(v_a_301_, v___x_323_);
v___x_328_ = l_Lean_Expr_cleanupAnnotations(v_type_314_);
v___x_329_ = l_Lean_Expr_isApp(v___x_328_);
if (v___x_329_ == 0)
{
lean_dec_ref(v___x_328_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_325_;
}
else
{
lean_object* v_arg_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_arg_330_ = lean_ctor_get(v___x_328_, 1);
lean_inc_ref(v_arg_330_);
v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_328_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_325_;
}
else
{
lean_object* v_arg_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_arg_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_arg_333_);
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_335_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_325_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_337_);
lean_dec_ref(v___x_336_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_325_;
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = l_Lean_Expr_cleanupAnnotations(v_arg_333_);
v___x_340_ = l_Lean_Expr_isApp(v___x_339_);
if (v___x_340_ == 0)
{
lean_dec_ref(v___x_339_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_309_;
}
else
{
lean_object* v_arg_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_arg_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc_ref(v_arg_341_);
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_339_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_309_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_345_, v___x_346_);
lean_dec_ref(v___x_345_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_330_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
goto v___jp_309_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = l_Lean_Expr_cleanupAnnotations(v_arg_330_);
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_349_);
lean_dec_ref(v___x_348_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
lean_inc_ref(v_arg_344_);
v___x_353_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_344_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8);
lean_inc_ref(v_value_315_);
lean_inc_ref_n(v_arg_341_, 2);
lean_inc_ref(v_arg_344_);
v___x_356_ = l_Lean_mkApp3(v___x_355_, v_arg_344_, v_arg_341_, v_value_315_);
v___x_357_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_341_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_374_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v_source_316_);
lean_inc_ref(v___x_362_);
lean_inc(v_name_313_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 3, v___x_362_);
lean_ctor_set(v___x_318_, 2, v___x_356_);
lean_ctor_set(v___x_318_, 1, v_a_354_);
v___x_364_ = v___x_318_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_name_313_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_a_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v___x_362_);
v___x_364_ = v_reuseFailAlloc_373_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11);
v___x_366_ = l_Lean_mkApp3(v___x_365_, v_arg_344_, v_arg_341_, v_value_315_);
v___x_367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_367_, 0, v_name_313_);
lean_ctor_set(v___x_367_, 1, v_a_358_);
lean_ctor_set(v___x_367_, 2, v___x_366_);
lean_ctor_set(v___x_367_, 3, v___x_362_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_364_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_369_);
v___x_371_ = v___x_360_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v___x_356_);
lean_dec(v_a_354_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
v_a_375_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_357_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_357_);
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
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec(v_name_313_);
v_a_383_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_353_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_353_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
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
v___jp_325_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_del_object(v___x_318_);
lean_dec_ref(v_source_316_);
lean_dec_ref(v_value_315_);
lean_dec_ref(v_type_314_);
lean_dec(v_name_313_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object* v_hyp_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(lean_object* v_hyp_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_404_, v_a_406_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(lean_object* v_hyp_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(v_hyp_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec(v_a_418_);
return v_res_429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_431_, v_a_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___boxed(lean_object* v_00_u03b2_434_, lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(v_00_u03b2_434_, v_m_435_, v_a_436_);
lean_dec_ref(v_a_436_);
lean_dec_ref(v_m_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1(lean_object* v_00_u03b2_439_, lean_object* v_m_440_, lean_object* v_a_441_, lean_object* v_b_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v_m_440_, v_a_441_, v_b_442_);
return v___x_443_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(lean_object* v_00_u03b2_444_, lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_448_, lean_object* v_a_449_, lean_object* v_x_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(v_00_u03b2_448_, v_a_449_, v_x_450_);
lean_dec(v_x_450_);
lean_dec_ref(v_a_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2(lean_object* v_00_u03b2_453_, lean_object* v_data_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_data_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_456_, lean_object* v_i_457_, lean_object* v_source_458_, lean_object* v_target_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v_i_457_, v_source_458_, v_target_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(lean_object* v_worklist_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
if (lean_obj_tag(v_worklist_465_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v_head_477_; lean_object* v_tail_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_510_; 
v_head_477_ = lean_ctor_get(v_worklist_465_, 0);
v_tail_478_ = lean_ctor_get(v_worklist_465_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_worklist_465_);
if (v_isSharedCheck_510_ == 0)
{
v___x_480_ = v_worklist_465_;
v_isShared_481_ = v_isSharedCheck_510_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_tail_478_);
lean_inc(v_head_477_);
lean_dec(v_worklist_465_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_510_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; 
lean_inc(v_head_477_);
v___x_482_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_head_477_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
if (lean_obj_tag(v_a_483_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_del_object(v___x_480_);
v___x_484_ = lean_st_ref_take(v_a_466_);
v___x_485_ = lean_array_push(v___x_484_, v_head_477_);
v___x_486_ = lean_st_ref_set(v_a_466_, v___x_485_);
v_worklist_465_ = v_tail_478_;
goto _start;
}
else
{
lean_object* v_val_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_head_477_);
v_val_488_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_a_483_, 1);
v_fst_489_ = lean_ctor_get(v_val_488_, 0);
v_snd_490_ = lean_ctor_get(v_val_488_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_val_488_);
if (v_isSharedCheck_501_ == 0)
{
v___x_492_ = v_val_488_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_val_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_snd_490_);
v___x_495_ = v___x_480_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_snd_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_tail_478_);
v___x_495_ = v_reuseFailAlloc_500_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 1);
lean_ctor_set(v___x_492_, 1, v___x_495_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v_worklist_465_ = v___x_497_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_480_);
lean_dec(v_tail_478_);
lean_dec(v_head_477_);
v_a_502_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_482_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_482_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object* v_worklist_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec(v_a_512_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(lean_object* v_worklist_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_522_, v_a_523_, v_a_524_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(lean_object* v_worklist_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(v_worklist_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(lean_object* v_hyp_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; 
lean_inc_ref(v_hyp_548_);
v___x_558_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_548_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_585_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_585_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_585_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_585_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_val_563_; lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
lean_del_object(v___x_561_);
lean_dec_ref(v_hyp_548_);
v_val_563_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v_a_559_, 1);
v_fst_564_ = lean_ctor_get(v_val_563_, 0);
v_snd_565_ = lean_ctor_get(v_val_563_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_val_563_);
if (v_isSharedCheck_575_ == 0)
{
v___x_567_ = v_val_563_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_inc(v_fst_564_);
lean_dec(v_val_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 1, v___x_569_);
lean_ctor_set(v___x_567_, 0, v_snd_565_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_snd_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_574_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_fst_564_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v___x_572_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
return v___x_573_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec(v_a_559_);
v___x_576_ = lean_st_ref_take(v_a_549_);
lean_dec(v___x_576_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_array_push(v___x_578_, v_hyp_548_);
v___x_580_ = lean_st_ref_set(v_a_549_, v___x_579_);
v___x_581_ = lean_box(0);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_581_);
v___x_583_ = v___x_561_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_hyp_548_);
v_a_586_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_558_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_558_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg___boxed(lean_object* v_hyp_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec(v_a_595_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(lean_object* v_hyp_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_605_, v_a_606_, v_a_607_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___boxed(lean_object* v_hyp_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(v_hyp_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec(v_a_619_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
lean_inc(v___y_632_);
v___x_642_ = lean_apply_10(v_x_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, lean_box(0));
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed(lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(v_x_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(lean_object* v_mvarId_655_, lean_object* v_x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___f_667_; lean_object* v___x_668_; 
lean_inc(v___y_661_);
lean_inc_ref(v___y_660_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
lean_inc(v___y_657_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_667_, 0, v_x_656_);
lean_closure_set(v___f_667_, 1, v___y_657_);
lean_closure_set(v___f_667_, 2, v___y_658_);
lean_closure_set(v___f_667_, 3, v___y_659_);
lean_closure_set(v___f_667_, 4, v___y_660_);
lean_closure_set(v___f_667_, 5, v___y_661_);
v___x_668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_655_, v___f_667_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_668_) == 0)
{
return v___x_668_;
}
else
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
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___boxed(lean_object* v_mvarId_677_, lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_677_, v_x_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(lean_object* v_00_u03b1_690_, lean_object* v_mvarId_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___boxed(lean_object* v_00_u03b1_704_, lean_object* v_mvarId_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(v_00_u03b1_704_, v_mvarId_705_, v_x_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(lean_object* v_hyps_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; lean_object* v_rewriteSimpCache_730_; lean_object* v_rewriteDSimpCache_731_; lean_object* v_acCache_732_; lean_object* v_typeAnalysis_733_; lean_object* v_goal_734_; uint8_t v_didChange_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_745_; 
v___x_729_ = lean_st_ref_take(v___y_721_);
v_rewriteSimpCache_730_ = lean_ctor_get(v___x_729_, 0);
v_rewriteDSimpCache_731_ = lean_ctor_get(v___x_729_, 1);
v_acCache_732_ = lean_ctor_get(v___x_729_, 2);
v_typeAnalysis_733_ = lean_ctor_get(v___x_729_, 3);
v_goal_734_ = lean_ctor_get(v___x_729_, 4);
v_didChange_735_ = lean_ctor_get_uint8(v___x_729_, sizeof(void*)*6);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_729_, 5);
lean_dec(v_unused_746_);
v___x_737_ = v___x_729_;
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_goal_734_);
lean_inc(v_typeAnalysis_733_);
lean_inc(v_acCache_732_);
lean_inc(v_rewriteDSimpCache_731_);
lean_inc(v_rewriteSimpCache_730_);
lean_dec(v___x_729_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 5, v_hyps_718_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_rewriteSimpCache_730_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_rewriteDSimpCache_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_acCache_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_typeAnalysis_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_goal_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 5, v_hyps_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*6, v_didChange_735_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_st_ref_set(v___y_721_, v___x_740_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed(lean_object* v_hyps_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(v_hyps_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(uint8_t v___x_759_, lean_object* v_val_760_, lean_object* v_____r_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_rewriteSimpCache_773_; lean_object* v_rewriteDSimpCache_774_; lean_object* v_acCache_775_; lean_object* v_typeAnalysis_776_; lean_object* v_goal_777_; lean_object* v_hypotheses_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v___x_772_ = lean_st_ref_take(v___y_764_);
v_rewriteSimpCache_773_ = lean_ctor_get(v___x_772_, 0);
v_rewriteDSimpCache_774_ = lean_ctor_get(v___x_772_, 1);
v_acCache_775_ = lean_ctor_get(v___x_772_, 2);
v_typeAnalysis_776_ = lean_ctor_get(v___x_772_, 3);
v_goal_777_ = lean_ctor_get(v___x_772_, 4);
v_hypotheses_778_ = lean_ctor_get(v___x_772_, 5);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v___x_772_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_hypotheses_778_);
lean_inc(v_goal_777_);
lean_inc(v_typeAnalysis_776_);
lean_inc(v_acCache_775_);
lean_inc(v_rewriteDSimpCache_774_);
lean_inc(v_rewriteSimpCache_773_);
lean_dec(v___x_772_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_rewriteSimpCache_773_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_rewriteDSimpCache_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_acCache_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_typeAnalysis_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_goal_777_);
lean_ctor_set(v_reuseFailAlloc_786_, 5, v_hypotheses_778_);
v___x_783_ = v_reuseFailAlloc_786_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*6, v___x_759_);
v___x_784_ = lean_st_ref_set(v___y_764_, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_val_760_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0___boxed(lean_object* v___x_788_, lean_object* v_val_789_, lean_object* v_____r_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v___x_40703__boxed_801_; lean_object* v_res_802_; 
v___x_40703__boxed_801_ = lean_unbox(v___x_788_);
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_40703__boxed_801_, v_val_789_, v_____r_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(lean_object* v_msgData_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v_env_810_; lean_object* v___x_811_; lean_object* v_mctx_812_; lean_object* v_lctx_813_; lean_object* v_options_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_809_ = lean_st_ref_get(v___y_807_);
v_env_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_env_810_);
lean_dec(v___x_809_);
v___x_811_ = lean_st_ref_get(v___y_805_);
v_mctx_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_mctx_812_);
lean_dec(v___x_811_);
v_lctx_813_ = lean_ctor_get(v___y_804_, 2);
v_options_814_ = lean_ctor_get(v___y_806_, 2);
lean_inc_ref(v_options_814_);
lean_inc_ref(v_lctx_813_);
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v_env_810_);
lean_ctor_set(v___x_815_, 1, v_mctx_812_);
lean_ctor_set(v___x_815_, 2, v_lctx_813_);
lean_ctor_set(v___x_815_, 3, v_options_814_);
v___x_816_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_msgData_803_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0___boxed(lean_object* v_msgData_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msgData_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_825_; double v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_float_of_nat(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(lean_object* v_cls_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_ref_837_; lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_883_; 
v_ref_837_ = lean_ctor_get(v___y_834_, 5);
v___x_838_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_883_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_883_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_traceState_844_; lean_object* v_env_845_; lean_object* v_nextMacroScope_846_; lean_object* v_ngen_847_; lean_object* v_auxDeclNGen_848_; lean_object* v_cache_849_; lean_object* v_messages_850_; lean_object* v_infoState_851_; lean_object* v_snapshotTasks_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_882_; 
v___x_843_ = lean_st_ref_take(v___y_835_);
v_traceState_844_ = lean_ctor_get(v___x_843_, 4);
v_env_845_ = lean_ctor_get(v___x_843_, 0);
v_nextMacroScope_846_ = lean_ctor_get(v___x_843_, 1);
v_ngen_847_ = lean_ctor_get(v___x_843_, 2);
v_auxDeclNGen_848_ = lean_ctor_get(v___x_843_, 3);
v_cache_849_ = lean_ctor_get(v___x_843_, 5);
v_messages_850_ = lean_ctor_get(v___x_843_, 6);
v_infoState_851_ = lean_ctor_get(v___x_843_, 7);
v_snapshotTasks_852_ = lean_ctor_get(v___x_843_, 8);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_882_ == 0)
{
v___x_854_ = v___x_843_;
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snapshotTasks_852_);
lean_inc(v_infoState_851_);
lean_inc(v_messages_850_);
lean_inc(v_cache_849_);
lean_inc(v_traceState_844_);
lean_inc(v_auxDeclNGen_848_);
lean_inc(v_ngen_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_env_845_);
lean_dec(v___x_843_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_882_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint64_t v_tid_856_; lean_object* v_traces_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_881_; 
v_tid_856_ = lean_ctor_get_uint64(v_traceState_844_, sizeof(void*)*1);
v_traces_857_ = lean_ctor_get(v_traceState_844_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_traceState_844_);
if (v_isSharedCheck_881_ == 0)
{
v___x_859_ = v_traceState_844_;
v_isShared_860_ = v_isSharedCheck_881_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_traces_857_);
lean_dec(v_traceState_844_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_881_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; double v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_861_ = lean_box(0);
v___x_862_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0);
v___x_863_ = 0;
v___x_864_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1));
v___x_865_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_865_, 0, v_cls_830_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
lean_ctor_set_float(v___x_865_, sizeof(void*)*3, v___x_862_);
lean_ctor_set_float(v___x_865_, sizeof(void*)*3 + 8, v___x_862_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*3 + 16, v___x_863_);
v___x_866_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2));
v___x_867_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v_a_839_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_inc(v_ref_837_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_ref_837_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_PersistentArray_push___redArg(v_traces_857_, v___x_868_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_869_);
v___x_871_ = v___x_859_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_869_);
lean_ctor_set_uint64(v_reuseFailAlloc_880_, sizeof(void*)*1, v_tid_856_);
v___x_871_ = v_reuseFailAlloc_880_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 4, v___x_871_);
v___x_873_ = v___x_854_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_845_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_847_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_848_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v_cache_849_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_messages_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_infoState_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_snapshotTasks_852_);
v___x_873_ = v_reuseFailAlloc_879_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_st_ref_set(v___y_835_, v___x_873_);
v___x_875_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_875_);
v___x_877_ = v___x_841_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___boxed(lean_object* v_cls_884_, lean_object* v_msg_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_884_, v_msg_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_891_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5(void){
_start:
{
lean_object* v_cls_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_cls_901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4));
v___x_903_ = l_Lean_Name_append(v___x_902_, v_cls_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(lean_object* v_a_907_, lean_object* v_as_908_, size_t v_i_909_, size_t v_stop_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_a_923_; uint8_t v___x_929_; 
v___x_929_ = lean_usize_dec_eq(v_i_909_, v_stop_910_);
if (v___x_929_ == 0)
{
lean_object* v_options_930_; uint8_t v_hasTrace_931_; 
v_options_930_ = lean_ctor_get(v___y_919_, 2);
v_hasTrace_931_ = lean_ctor_get_uint8(v_options_930_, sizeof(void*)*1);
if (v_hasTrace_931_ == 0)
{
goto v___jp_927_;
}
else
{
lean_object* v_inheritedTraceOptions_932_; lean_object* v_cls_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_inheritedTraceOptions_932_ = lean_ctor_get(v___y_919_, 13);
v_cls_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_934_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_935_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_932_, v_options_930_, v___x_934_);
if (v___x_935_ == 0)
{
goto v___jp_927_;
}
else
{
lean_object* v_type_936_; lean_object* v___x_937_; lean_object* v_type_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_type_936_ = lean_ctor_get(v_a_907_, 1);
v___x_937_ = lean_array_uget_borrowed(v_as_908_, v_i_909_);
v_type_938_ = lean_ctor_get(v___x_937_, 1);
lean_inc_ref(v_type_936_);
v___x_939_ = l_Lean_MessageData_ofExpr(v_type_936_);
v___x_940_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
lean_inc_ref(v_type_938_);
v___x_942_ = l_Lean_MessageData_ofExpr(v_type_938_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_933_, v___x_943_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v_a_923_ = v_a_945_;
goto v___jp_922_;
}
else
{
lean_dec_ref(v_a_907_);
return v___x_944_;
}
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec_ref(v_a_907_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_911_);
return v___x_946_;
}
v___jp_922_:
{
size_t v___x_924_; size_t v___x_925_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_909_, v___x_924_);
v_i_909_ = v___x_925_;
v_b_911_ = v_a_923_;
goto _start;
}
v___jp_927_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_box(0);
v_a_923_ = v___x_928_;
goto v___jp_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___boxed(lean_object* v_a_947_, lean_object* v_as_948_, lean_object* v_i_949_, lean_object* v_stop_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
size_t v_i_boxed_962_; size_t v_stop_boxed_963_; lean_object* v_res_964_; 
v_i_boxed_962_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_stop_boxed_963_ = lean_unbox_usize(v_stop_950_);
lean_dec(v_stop_950_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v_a_947_, v_as_948_, v_i_boxed_962_, v_stop_boxed_963_, v_b_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v_as_948_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1(uint8_t v_isZero_965_, lean_object* v_val_966_, lean_object* v_____r_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_rewriteSimpCache_979_; lean_object* v_rewriteDSimpCache_980_; lean_object* v_acCache_981_; lean_object* v_typeAnalysis_982_; lean_object* v_goal_983_; lean_object* v_hypotheses_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
v___x_978_ = lean_st_ref_take(v___y_970_);
v_rewriteSimpCache_979_ = lean_ctor_get(v___x_978_, 0);
v_rewriteDSimpCache_980_ = lean_ctor_get(v___x_978_, 1);
v_acCache_981_ = lean_ctor_get(v___x_978_, 2);
v_typeAnalysis_982_ = lean_ctor_get(v___x_978_, 3);
v_goal_983_ = lean_ctor_get(v___x_978_, 4);
v_hypotheses_984_ = lean_ctor_get(v___x_978_, 5);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_993_ == 0)
{
v___x_986_ = v___x_978_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_hypotheses_984_);
lean_inc(v_goal_983_);
lean_inc(v_typeAnalysis_982_);
lean_inc(v_acCache_981_);
lean_inc(v_rewriteDSimpCache_980_);
lean_inc(v_rewriteSimpCache_979_);
lean_dec(v___x_978_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_rewriteSimpCache_979_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_rewriteDSimpCache_980_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_acCache_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_typeAnalysis_982_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_goal_983_);
lean_ctor_set(v_reuseFailAlloc_992_, 5, v_hypotheses_984_);
v___x_989_ = v_reuseFailAlloc_992_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*6, v_isZero_965_);
v___x_990_ = lean_st_ref_set(v___y_970_, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_val_966_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1___boxed(lean_object* v_isZero_994_, lean_object* v_val_995_, lean_object* v_____r_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v_isZero_boxed_1007_; lean_object* v_res_1008_; 
v_isZero_boxed_1007_ = lean_unbox(v_isZero_994_);
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1(v_isZero_boxed_1007_, v_val_995_, v_____r_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(lean_object* v_as_1011_, size_t v_i_1012_, size_t v_stop_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_a_1026_; lean_object* v___y_1032_; uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_eq(v_i_1012_, v_stop_1013_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
v___x_1037_ = lean_st_mk_ref(v___x_1036_);
v___x_1038_ = lean_array_uget_borrowed(v_as_1011_, v_i_1012_);
lean_inc(v___x_1038_);
v___x_1039_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v___x_1038_, v___x_1037_, v___y_1015_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v_isZero_1042_; 
lean_dec_ref_known(v___x_1039_, 1);
v___x_1040_ = lean_st_ref_get(v___x_1037_);
lean_dec(v___x_1037_);
v___x_1041_ = lean_array_get_size(v___x_1040_);
v_isZero_1042_ = lean_nat_dec_eq(v___x_1041_, v___x_1035_);
if (v_isZero_1042_ == 1)
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_nat_dec_lt(v___x_1035_, v___x_1041_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_rewriteSimpCache_1045_; lean_object* v_rewriteDSimpCache_1046_; lean_object* v_acCache_1047_; lean_object* v_typeAnalysis_1048_; lean_object* v_goal_1049_; lean_object* v_hypotheses_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v___x_1044_ = lean_st_ref_take(v___y_1017_);
v_rewriteSimpCache_1045_ = lean_ctor_get(v___x_1044_, 0);
v_rewriteDSimpCache_1046_ = lean_ctor_get(v___x_1044_, 1);
v_acCache_1047_ = lean_ctor_get(v___x_1044_, 2);
v_typeAnalysis_1048_ = lean_ctor_get(v___x_1044_, 3);
v_goal_1049_ = lean_ctor_get(v___x_1044_, 4);
v_hypotheses_1050_ = lean_ctor_get(v___x_1044_, 5);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1052_ = v___x_1044_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_hypotheses_1050_);
lean_inc(v_goal_1049_);
lean_inc(v_typeAnalysis_1048_);
lean_inc(v_acCache_1047_);
lean_inc(v_rewriteDSimpCache_1046_);
lean_inc(v_rewriteSimpCache_1045_);
lean_dec(v___x_1044_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_rewriteSimpCache_1045_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_rewriteDSimpCache_1046_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_acCache_1047_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_typeAnalysis_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_goal_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 5, v_hypotheses_1050_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*6, v_isZero_1042_);
v___x_1056_ = lean_st_ref_set(v___y_1017_, v___x_1055_);
v_a_1026_ = v___x_1040_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_nat_dec_le(v___x_1041_, v___x_1041_);
if (v___x_1060_ == 0)
{
if (v___x_1043_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1043_, v___x_1040_, v___x_1059_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1061_;
goto v___jp_1031_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v___x_1038_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1038_, v___x_1040_, v___x_1062_, v___x_1063_, v___x_1059_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1043_, v___x_1040_, v_a_1065_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1066_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_b_1014_);
v_a_1067_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1064_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1064_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
else
{
size_t v___x_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v___x_1038_);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1038_, v___x_1040_, v___x_1075_, v___x_1076_, v___x_1059_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1043_, v___x_1040_, v_a_1078_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1079_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_b_1014_);
v_a_1080_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1077_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
else
{
lean_object* v_one_1088_; lean_object* v_n_1089_; uint8_t v_isZero_1090_; 
v_one_1088_ = lean_unsigned_to_nat(1u);
v_n_1089_ = lean_nat_sub(v___x_1041_, v_one_1088_);
v_isZero_1090_ = lean_nat_dec_eq(v_n_1089_, v___x_1035_);
lean_dec(v_n_1089_);
if (v_isZero_1090_ == 1)
{
lean_object* v_newHyp_1091_; lean_object* v_type_1092_; lean_object* v_type_1093_; uint8_t v___x_1094_; 
v_newHyp_1091_ = lean_array_fget(v___x_1040_, v___x_1035_);
v_type_1092_ = lean_ctor_get(v_newHyp_1091_, 1);
lean_inc_ref(v_type_1092_);
lean_dec(v_newHyp_1091_);
v_type_1093_ = lean_ctor_get(v___x_1038_, 1);
v___x_1094_ = lean_expr_eqv(v_type_1092_, v_type_1093_);
if (v___x_1094_ == 0)
{
lean_object* v_options_1095_; lean_object* v_inheritedTraceOptions_1096_; uint8_t v_hasTrace_1097_; 
v_options_1095_ = lean_ctor_get(v___y_1022_, 2);
v_inheritedTraceOptions_1096_ = lean_ctor_get(v___y_1022_, 13);
v_hasTrace_1097_ = lean_ctor_get_uint8(v_options_1095_, sizeof(void*)*1);
if (v_hasTrace_1097_ == 0)
{
lean_dec_ref(v_type_1092_);
goto v___jp_1098_;
}
else
{
lean_object* v_cls_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_cls_1101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_1102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_1103_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1096_, v_options_1095_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_type_1092_);
goto v___jp_1098_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_type_1093_);
v___x_1104_ = l_Lean_MessageData_ofExpr(v_type_1093_);
v___x_1105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_MessageData_ofExpr(v_type_1092_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1101_, v___x_1108_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1(v_isZero_1090_, v___x_1040_, v_a_1110_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1111_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_b_1014_);
v_a_1112_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1109_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
v___jp_1098_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_box(0);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__1(v_isZero_1090_, v___x_1040_, v___x_1099_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1100_;
goto v___jp_1031_;
}
}
else
{
lean_dec_ref(v_type_1092_);
v_a_1026_ = v___x_1040_;
goto v___jp_1025_;
}
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_lt(v___x_1035_, v___x_1041_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v_rewriteSimpCache_1122_; lean_object* v_rewriteDSimpCache_1123_; lean_object* v_acCache_1124_; lean_object* v_typeAnalysis_1125_; lean_object* v_goal_1126_; lean_object* v_hypotheses_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v___x_1121_ = lean_st_ref_take(v___y_1017_);
v_rewriteSimpCache_1122_ = lean_ctor_get(v___x_1121_, 0);
v_rewriteDSimpCache_1123_ = lean_ctor_get(v___x_1121_, 1);
v_acCache_1124_ = lean_ctor_get(v___x_1121_, 2);
v_typeAnalysis_1125_ = lean_ctor_get(v___x_1121_, 3);
v_goal_1126_ = lean_ctor_get(v___x_1121_, 4);
v_hypotheses_1127_ = lean_ctor_get(v___x_1121_, 5);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v___x_1121_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_hypotheses_1127_);
lean_inc(v_goal_1126_);
lean_inc(v_typeAnalysis_1125_);
lean_inc(v_acCache_1124_);
lean_inc(v_rewriteDSimpCache_1123_);
lean_inc(v_rewriteSimpCache_1122_);
lean_dec(v___x_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = 1;
if (v_isShared_1130_ == 0)
{
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_rewriteSimpCache_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_rewriteDSimpCache_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_acCache_1124_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_typeAnalysis_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_goal_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_hypotheses_1127_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*6, v___x_1131_);
v___x_1134_ = lean_st_ref_set(v___y_1017_, v___x_1133_);
v_a_1026_ = v___x_1040_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_nat_dec_le(v___x_1041_, v___x_1041_);
if (v___x_1138_ == 0)
{
if (v___x_1120_ == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1120_, v___x_1040_, v___x_1137_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1139_;
goto v___jp_1031_;
}
else
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v___x_1038_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1038_, v___x_1040_, v___x_1140_, v___x_1141_, v___x_1137_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1120_, v___x_1040_, v_a_1143_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1144_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_b_1014_);
v_a_1145_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1142_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1142_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = lean_usize_of_nat(v___x_1041_);
lean_inc(v___x_1038_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1038_, v___x_1040_, v___x_1153_, v___x_1154_, v___x_1137_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v___x_1120_, v___x_1040_, v_a_1156_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
v___y_1032_ = v___x_1157_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v___x_1040_);
lean_dec_ref(v_b_1014_);
v_a_1158_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1155_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1155_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
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
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v___x_1037_);
lean_dec_ref(v_b_1014_);
v_a_1166_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1039_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1039_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_b_1014_);
return v___x_1174_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; 
v___x_1027_ = l_Array_append___redArg(v_b_1014_, v_a_1026_);
lean_dec_ref(v_a_1026_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1012_, v___x_1028_);
v_i_1012_ = v___x_1029_;
v_b_1014_ = v___x_1027_;
goto _start;
}
v___jp_1031_:
{
if (lean_obj_tag(v___y_1032_) == 0)
{
lean_object* v_a_1033_; 
v_a_1033_ = lean_ctor_get(v___y_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___y_1032_, 1);
v_a_1026_ = v_a_1033_;
goto v___jp_1025_;
}
else
{
lean_dec_ref(v_b_1014_);
return v___y_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___boxed(lean_object* v_as_1175_, lean_object* v_i_1176_, lean_object* v_stop_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
size_t v_i_boxed_1189_; size_t v_stop_boxed_1190_; lean_object* v_res_1191_; 
v_i_boxed_1189_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_stop_boxed_1190_ = lean_unbox_usize(v_stop_1177_);
lean_dec(v_stop_1177_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_as_1175_, v_i_boxed_1189_, v_stop_boxed_1190_, v_b_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v_as_1175_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1(lean_object* v___f_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_hypotheses_1206_; lean_object* v___x_1207_; lean_object* v_rewriteSimpCache_1208_; lean_object* v_rewriteDSimpCache_1209_; lean_object* v_acCache_1210_; lean_object* v_typeAnalysis_1211_; lean_object* v_goal_1212_; uint8_t v_didChange_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1272_; 
v___x_1205_ = lean_st_ref_get(v___y_1197_);
v_hypotheses_1206_ = lean_ctor_get(v___x_1205_, 5);
lean_inc_ref(v_hypotheses_1206_);
lean_dec(v___x_1205_);
v___x_1207_ = lean_st_ref_take(v___y_1197_);
v_rewriteSimpCache_1208_ = lean_ctor_get(v___x_1207_, 0);
v_rewriteDSimpCache_1209_ = lean_ctor_get(v___x_1207_, 1);
v_acCache_1210_ = lean_ctor_get(v___x_1207_, 2);
v_typeAnalysis_1211_ = lean_ctor_get(v___x_1207_, 3);
v_goal_1212_ = lean_ctor_get(v___x_1207_, 4);
v_didChange_1213_ = lean_ctor_get_uint8(v___x_1207_, sizeof(void*)*6);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1207_, 5);
lean_dec(v_unused_1273_);
v___x_1215_ = v___x_1207_;
v_isShared_1216_ = v_isSharedCheck_1272_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_goal_1212_);
lean_inc(v_typeAnalysis_1211_);
lean_inc(v_acCache_1210_);
lean_inc(v_rewriteDSimpCache_1209_);
lean_inc(v_rewriteSimpCache_1208_);
lean_dec(v___x_1207_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1272_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 5, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_rewriteSimpCache_1208_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_rewriteDSimpCache_1209_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_acCache_1210_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_typeAnalysis_1211_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_goal_1212_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v___x_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1271_, sizeof(void*)*6, v_didChange_1213_);
v___x_1220_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1221_ = lean_st_ref_set(v___y_1197_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___closed__0));
v___x_1223_ = lean_array_get_size(v_hypotheses_1206_);
v___x_1224_ = lean_nat_dec_lt(v___x_1217_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_rewriteSimpCache_1226_; lean_object* v_rewriteDSimpCache_1227_; lean_object* v_acCache_1228_; lean_object* v_typeAnalysis_1229_; lean_object* v_goal_1230_; uint8_t v_didChange_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_hypotheses_1206_);
lean_dec_ref(v___f_1194_);
v___x_1225_ = lean_st_ref_take(v___y_1197_);
v_rewriteSimpCache_1226_ = lean_ctor_get(v___x_1225_, 0);
v_rewriteDSimpCache_1227_ = lean_ctor_get(v___x_1225_, 1);
v_acCache_1228_ = lean_ctor_get(v___x_1225_, 2);
v_typeAnalysis_1229_ = lean_ctor_get(v___x_1225_, 3);
v_goal_1230_ = lean_ctor_get(v___x_1225_, 4);
v_didChange_1231_ = lean_ctor_get_uint8(v___x_1225_, sizeof(void*)*6);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1225_, 5);
lean_dec(v_unused_1242_);
v___x_1233_ = v___x_1225_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_goal_1230_);
lean_inc(v_typeAnalysis_1229_);
lean_inc(v_acCache_1228_);
lean_inc(v_rewriteDSimpCache_1227_);
lean_inc(v_rewriteSimpCache_1226_);
lean_dec(v___x_1225_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 5, v___x_1222_);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_rewriteSimpCache_1226_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_rewriteDSimpCache_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_acCache_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_typeAnalysis_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_goal_1230_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v___x_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1240_, sizeof(void*)*6, v_didChange_1231_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_st_ref_set(v___y_1197_, v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
}
else
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_nat_dec_le(v___x_1223_, v___x_1223_);
if (v___x_1243_ == 0)
{
if (v___x_1224_ == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref(v_hypotheses_1206_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
v___x_1244_ = lean_apply_11(v___f_1194_, v___x_1222_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1244_;
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = lean_usize_of_nat(v___x_1223_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_hypotheses_1206_, v___x_1245_, v___x_1246_, v___x_1222_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec_ref(v_hypotheses_1206_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
v___x_1249_ = lean_apply_11(v___f_1194_, v_a_1248_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v___f_1194_);
v_a_1250_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1247_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_of_nat(v___x_1223_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_hypotheses_1206_, v___x_1258_, v___x_1259_, v___x_1222_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec_ref(v_hypotheses_1206_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
v___x_1262_ = lean_apply_11(v___f_1194_, v_a_1261_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1262_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v___f_1194_);
v_a_1263_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1260_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1260_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1___boxed(lean_object* v___f_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__1(v___f_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(lean_object* v_g_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___f_1300_; lean_object* v___x_1301_; 
v___f_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__1));
v___x_1301_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_g_1289_, v___f_1300_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___boxed(lean_object* v_g_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v_g_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(lean_object* v_cls_1314_, lean_object* v_msg_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1314_, v_msg_1315_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___boxed(lean_object* v_cls_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(v_cls_1327_, v_msg_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
return v_res_1339_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_unsigned_to_nat(16u);
v___x_1342_ = lean_mk_array(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v_goal_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1355_ = lean_st_ref_get(v___y_1347_);
v_goal_1356_ = lean_ctor_get(v___x_1355_, 4);
lean_inc(v_goal_1356_);
lean_dec(v___x_1355_);
v___x_1357_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1);
v___x_1358_ = lean_st_mk_ref(v___x_1357_);
v___x_1359_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v_goal_1356_, v___x_1358_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1369_; 
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1370_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1363_ = lean_st_ref_get(v___x_1358_);
lean_dec(v___x_1358_);
lean_dec(v___x_1363_);
v___x_1364_ = 0;
v___x_1365_ = lean_box(v___x_1364_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1365_);
v___x_1367_ = v___x_1361_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v___x_1358_);
v_a_1371_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1359_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1359_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1388_;
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
