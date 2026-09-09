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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached(lean_object* v_e_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = lean_st_ref_get(v_a_17_);
v___f_31_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_32_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_33_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_31_, v___f_32_, v___x_30_, v_e_16_);
lean_dec(v___x_30_);
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
lean_object* v___x_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_54_ = lean_st_ref_take(v_a_52_);
v___f_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_57_ = lean_box(0);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_55_, v___f_56_, v___x_54_, v_e_51_, v___x_57_);
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
lean_object* v___x_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_79_ = lean_st_ref_take(v_a_66_);
v___f_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__0));
v___f_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_FlattenM_isCached___redArg___closed__1));
v___x_82_ = lean_box(0);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_80_, v___f_81_, v___x_79_, v_e_65_, v___x_82_);
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
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_nbuckets_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_229_ = lean_array_get_size(v_data_228_);
v___x_230_ = lean_unsigned_to_nat(2u);
v_nbuckets_231_ = lean_nat_mul(v___x_229_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_box(0);
v___x_234_ = lean_mk_array(v_nbuckets_231_, v___x_233_);
v___x_235_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v___x_232_, v_data_228_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(lean_object* v_m_236_, lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_bkt_257_; uint8_t v___x_258_; 
v_size_239_ = lean_ctor_get(v_m_236_, 0);
v_buckets_240_ = lean_ctor_get(v_m_236_, 1);
v___x_241_ = lean_array_get_size(v_buckets_240_);
v___x_242_ = lean_ptr_addr(v_a_237_);
v___x_243_ = ((size_t)3ULL);
v___x_244_ = lean_usize_shift_right(v___x_242_, v___x_243_);
v___x_245_ = lean_usize_to_uint64(v___x_244_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_241_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v_bkt_257_ = lean_array_uget_borrowed(v_buckets_240_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_237_, v_bkt_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_279_; 
lean_inc_ref(v_buckets_240_);
lean_inc(v_size_239_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_m_236_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_280_ = lean_ctor_get(v_m_236_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_m_236_, 0);
lean_dec(v_unused_281_);
v___x_260_ = v_m_236_;
v_isShared_261_ = v_isSharedCheck_279_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_m_236_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_279_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v_size_x27_263_; lean_object* v___x_264_; lean_object* v_buckets_x27_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v_size_x27_263_ = lean_nat_add(v_size_239_, v___x_262_);
lean_dec(v_size_239_);
lean_inc(v_bkt_257_);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v_a_237_);
lean_ctor_set(v___x_264_, 1, v_b_238_);
lean_ctor_set(v___x_264_, 2, v_bkt_257_);
v_buckets_x27_265_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_264_);
v___x_266_ = lean_unsigned_to_nat(4u);
v___x_267_ = lean_nat_mul(v_size_x27_263_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(3u);
v___x_269_ = lean_nat_div(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_array_get_size(v_buckets_x27_265_);
v___x_271_ = lean_nat_dec_le(v___x_269_, v___x_270_);
lean_dec(v___x_269_);
if (v___x_271_ == 0)
{
lean_object* v_val_272_; lean_object* v___x_274_; 
v_val_272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_buckets_x27_265_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v_val_272_);
lean_ctor_set(v___x_260_, 0, v_size_x27_263_);
v___x_274_ = v___x_260_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_size_x27_263_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_val_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_277_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v_buckets_x27_265_);
lean_ctor_set(v___x_260_, 0, v_size_x27_263_);
v___x_277_ = v___x_260_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_size_x27_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_buckets_x27_265_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_dec(v_b_238_);
lean_dec_ref(v_a_237_);
return v_m_236_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_box(0);
v___x_299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__7));
v___x_300_ = l_Lean_mkConst(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__10));
v___x_311_ = l_Lean_mkConst(v___x_310_, v___x_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(lean_object* v_hyp_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_324_; lean_object* v_name_325_; lean_object* v_type_326_; lean_object* v_value_327_; lean_object* v_source_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_405_; 
v___x_324_ = lean_st_ref_get(v_a_313_);
v_name_325_ = lean_ctor_get(v_hyp_312_, 0);
v_type_326_ = lean_ctor_get(v_hyp_312_, 1);
v_value_327_ = lean_ctor_get(v_hyp_312_, 2);
v_source_328_ = lean_ctor_get(v_hyp_312_, 3);
v_isSharedCheck_405_ = !lean_is_exclusive(v_hyp_312_);
if (v_isSharedCheck_405_ == 0)
{
v___x_330_ = v_hyp_312_;
v_isShared_331_ = v_isSharedCheck_405_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_source_328_);
lean_inc(v_value_327_);
lean_inc(v_type_326_);
lean_inc(v_name_325_);
lean_dec(v_hyp_312_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_405_;
goto v_resetjp_329_;
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
v_resetjp_329_:
{
uint8_t v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v___x_324_, v_type_326_);
lean_dec(v___x_324_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_333_ = lean_st_ref_take(v_a_313_);
v___x_334_ = lean_box(0);
lean_inc_ref(v_type_326_);
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v___x_333_, v_type_326_, v___x_334_);
v___x_336_ = lean_st_ref_put(v_a_313_, v___x_335_);
v___x_340_ = l_Lean_Expr_cleanupAnnotations(v_type_326_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_337_;
}
else
{
lean_object* v_arg_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_arg_342_ = lean_ctor_get(v___x_340_, 1);
lean_inc_ref(v_arg_342_);
v___x_343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_344_ = l_Lean_Expr_isApp(v___x_343_);
if (v___x_344_ == 0)
{
lean_dec_ref(v___x_343_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_337_;
}
else
{
lean_object* v_arg_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_345_ = lean_ctor_get(v___x_343_, 1);
lean_inc_ref(v_arg_345_);
v___x_346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_343_);
v___x_347_ = l_Lean_Expr_isApp(v___x_346_);
if (v___x_347_ == 0)
{
lean_dec_ref(v___x_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_337_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_346_);
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__1));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_349_);
lean_dec_ref(v___x_348_);
if (v___x_350_ == 0)
{
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_337_;
}
else
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = l_Lean_Expr_cleanupAnnotations(v_arg_345_);
v___x_352_ = l_Lean_Expr_isApp(v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v___x_351_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_arg_353_ = lean_ctor_get(v___x_351_, 1);
lean_inc_ref(v_arg_353_);
v___x_354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_351_);
v___x_355_ = l_Lean_Expr_isApp(v___x_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v___x_354_);
lean_dec_ref(v_arg_353_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_arg_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc_ref(v_arg_356_);
v___x_357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_354_);
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__1));
v___x_359_ = l_Lean_Expr_isConstOf(v___x_357_, v___x_358_);
lean_dec_ref(v___x_357_);
if (v___x_359_ == 0)
{
lean_dec_ref(v_arg_356_);
lean_dec_ref(v_arg_353_);
lean_dec_ref(v_arg_342_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
goto v___jp_321_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = l_Lean_Expr_cleanupAnnotations(v_arg_342_);
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0___closed__9));
v___x_362_ = l_Lean_Expr_isConstOf(v___x_360_, v___x_361_);
lean_dec_ref(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v_arg_356_);
lean_dec_ref(v_arg_353_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
lean_inc_ref(v_arg_356_);
v___x_365_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_356_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v___x_367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__8);
lean_inc_ref(v_value_327_);
lean_inc_ref_n(v_arg_353_, 2);
lean_inc_ref(v_arg_356_);
v___x_368_ = l_Lean_mkApp3(v___x_367_, v_arg_356_, v_arg_353_, v_value_327_);
v___x_369_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___lam__0(v_arg_353_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_386_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_374_, 0, v_source_328_);
lean_inc_ref(v___x_374_);
lean_inc(v_name_325_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 3, v___x_374_);
lean_ctor_set(v___x_330_, 2, v___x_368_);
lean_ctor_set(v___x_330_, 1, v_a_366_);
v___x_376_ = v___x_330_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_name_325_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_a_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v___x_374_);
v___x_376_ = v_reuseFailAlloc_385_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___closed__11);
v___x_378_ = l_Lean_mkApp3(v___x_377_, v_arg_356_, v_arg_353_, v_value_327_);
v___x_379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_379_, 0, v_name_325_);
lean_ctor_set(v___x_379_, 1, v_a_370_);
lean_ctor_set(v___x_379_, 2, v___x_378_);
lean_ctor_set(v___x_379_, 3, v___x_374_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_376_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_381_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v___x_368_);
lean_dec(v_a_366_);
lean_dec_ref(v_arg_356_);
lean_dec_ref(v_arg_353_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
v_a_387_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_369_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_369_);
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
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_arg_356_);
lean_dec_ref(v_arg_353_);
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec(v_name_325_);
v_a_395_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_365_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_365_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
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
v___jp_337_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_del_object(v___x_330_);
lean_dec(v_source_328_);
lean_dec_ref(v_value_327_);
lean_dec_ref(v_type_326_);
lean_dec(v_name_325_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object* v_hyp_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(lean_object* v_hyp_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_416_, v_a_418_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___boxed(lean_object* v_hyp_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit(v_hyp_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec(v_a_433_);
return v_res_447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(lean_object* v_00_u03b2_448_, lean_object* v_m_449_, lean_object* v_a_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___redArg(v_m_449_, v_a_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0___boxed(lean_object* v_00_u03b2_452_, lean_object* v_m_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0(v_00_u03b2_452_, v_m_453_, v_a_454_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_m_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1(lean_object* v_00_u03b2_457_, lean_object* v_m_458_, lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1___redArg(v_m_458_, v_a_459_, v_b_460_);
return v___x_461_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___redArg(v_a_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__0_spec__0(v_00_u03b2_466_, v_a_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec_ref(v_a_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2(lean_object* v_00_u03b2_471_, lean_object* v_data_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2___redArg(v_data_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_474_, lean_object* v_i_475_, lean_object* v_source_476_, lean_object* v_target_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3___redArg(v_i_475_, v_source_476_, v_target_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_480_, v_x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(lean_object* v_worklist_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
if (lean_obj_tag(v_worklist_483_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_528_; 
v_head_495_ = lean_ctor_get(v_worklist_483_, 0);
v_tail_496_ = lean_ctor_get(v_worklist_483_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_worklist_483_);
if (v_isSharedCheck_528_ == 0)
{
v___x_498_ = v_worklist_483_;
v_isShared_499_ = v_isSharedCheck_528_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_tail_496_);
lean_inc(v_head_495_);
lean_dec(v_worklist_483_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_528_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
lean_inc(v_head_495_);
v___x_500_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_head_495_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_del_object(v___x_498_);
v___x_502_ = lean_st_ref_take(v_a_484_);
v___x_503_ = lean_array_push(v___x_502_, v_head_495_);
v___x_504_ = lean_st_ref_put(v_a_484_, v___x_503_);
v_worklist_483_ = v_tail_496_;
goto _start;
}
else
{
lean_object* v_val_506_; lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_head_495_);
v_val_506_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_501_, 1);
v_fst_507_ = lean_ctor_get(v_val_506_, 0);
v_snd_508_ = lean_ctor_get(v_val_506_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_val_506_);
if (v_isSharedCheck_519_ == 0)
{
v___x_510_ = v_val_506_;
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
lean_dec(v_val_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v_snd_508_);
v___x_513_ = v___x_498_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_snd_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_tail_496_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 1);
lean_ctor_set(v___x_510_, 1, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v_worklist_483_ = v___x_515_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_del_object(v___x_498_);
lean_dec(v_tail_496_);
lean_dec(v_head_495_);
v_a_520_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_500_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_500_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object* v_worklist_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec(v_a_530_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(lean_object* v_worklist_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v_worklist_540_, v_a_541_, v_a_542_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___boxed(lean_object* v_worklist_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds(v_worklist_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec(v_a_557_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(lean_object* v_hyp_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; 
lean_inc_ref(v_hyp_572_);
v___x_582_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_trySplit___redArg(v_hyp_572_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_609_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_609_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 1)
{
lean_object* v_val_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_585_);
lean_dec_ref(v_hyp_572_);
v_val_587_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v_a_583_, 1);
v_fst_588_ = lean_ctor_get(v_val_587_, 0);
v_snd_589_ = lean_ctor_get(v_val_587_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_val_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_591_ = v_val_587_;
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_inc(v_fst_588_);
lean_dec(v_val_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_599_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_box(0);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
lean_ctor_set(v___x_591_, 1, v___x_593_);
lean_ctor_set(v___x_591_, 0, v_snd_589_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_snd_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v_fst_588_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_splitAnds___redArg(v___x_596_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_a_583_);
v___x_600_ = lean_st_ref_take(v_a_573_);
lean_dec(v___x_600_);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_mk_empty_array_with_capacity(v___x_601_);
v___x_603_ = lean_array_push(v___x_602_, v_hyp_572_);
v___x_604_ = lean_st_ref_put(v_a_573_, v___x_603_);
v___x_605_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_605_);
v___x_607_ = v___x_585_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
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
lean_dec_ref(v_hyp_572_);
v_a_610_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_582_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_582_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg___boxed(lean_object* v_hyp_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec(v_a_619_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(lean_object* v_hyp_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v_hyp_629_, v_a_630_, v_a_631_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___boxed(lean_object* v_hyp_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp(v_hyp_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
v___x_675_ = lean_apply_13(v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, lean_box(0));
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed(lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0(v_x_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(lean_object* v_mvarId_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v___y_693_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_706_, 0, v_x_692_);
lean_closure_set(v___f_706_, 1, v___y_693_);
lean_closure_set(v___f_706_, 2, v___y_694_);
lean_closure_set(v___f_706_, 3, v___y_695_);
lean_closure_set(v___f_706_, 4, v___y_696_);
lean_closure_set(v___f_706_, 5, v___y_697_);
lean_closure_set(v___f_706_, 6, v___y_698_);
lean_closure_set(v___f_706_, 7, v___y_699_);
lean_closure_set(v___f_706_, 8, v___y_700_);
v___x_707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_691_, v___f_706_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_707_) == 0)
{
return v___x_707_;
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg___boxed(lean_object* v_mvarId_716_, lean_object* v_x_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_716_, v_x_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(lean_object* v_00_u03b1_732_, lean_object* v_mvarId_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_mvarId_733_, v_x_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___boxed(lean_object* v_00_u03b1_749_, lean_object* v_mvarId_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3(v_00_u03b1_749_, v_mvarId_750_, v_x_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(uint8_t v_isZero_766_, lean_object* v_val_767_, lean_object* v_____r_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_caches_783_; lean_object* v_typeAnalysis_784_; lean_object* v_target_785_; lean_object* v_hypotheses_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v___x_782_ = lean_st_ref_take(v___y_771_);
v_caches_783_ = lean_ctor_get(v___x_782_, 0);
v_typeAnalysis_784_ = lean_ctor_get(v___x_782_, 1);
v_target_785_ = lean_ctor_get(v___x_782_, 2);
v_hypotheses_786_ = lean_ctor_get(v___x_782_, 3);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_795_ == 0)
{
v___x_788_ = v___x_782_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_hypotheses_786_);
lean_inc(v_target_785_);
lean_inc(v_typeAnalysis_784_);
lean_inc(v_caches_783_);
lean_dec(v___x_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_caches_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_typeAnalysis_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_target_785_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_hypotheses_786_);
v___x_791_ = v_reuseFailAlloc_794_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*4, v_isZero_766_);
v___x_792_ = lean_st_ref_put(v___y_771_, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_val_767_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0___boxed(lean_object* v_isZero_796_, lean_object* v_val_797_, lean_object* v_____r_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v_isZero_boxed_812_; lean_object* v_res_813_; 
v_isZero_boxed_812_ = lean_unbox(v_isZero_796_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_boxed_812_, v_val_797_, v_____r_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(lean_object* v_msgData_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v_env_821_; lean_object* v___x_822_; lean_object* v_toCold_823_; lean_object* v_mctx_824_; lean_object* v_lctx_825_; lean_object* v_options_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_820_ = lean_st_ref_get(v___y_818_);
v_env_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_env_821_);
lean_dec(v___x_820_);
v___x_822_ = lean_st_ref_get(v___y_816_);
v_toCold_823_ = lean_ctor_get(v___y_817_, 0);
v_mctx_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref(v_mctx_824_);
lean_dec(v___x_822_);
v_lctx_825_ = lean_ctor_get(v___y_815_, 2);
v_options_826_ = lean_ctor_get(v_toCold_823_, 2);
lean_inc_ref(v_options_826_);
lean_inc_ref(v_lctx_825_);
v___x_827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_827_, 0, v_env_821_);
lean_ctor_set(v___x_827_, 1, v_mctx_824_);
lean_ctor_set(v___x_827_, 2, v_lctx_825_);
lean_ctor_set(v___x_827_, 3, v_options_826_);
v___x_828_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_msgData_814_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0___boxed(lean_object* v_msgData_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msgData_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_836_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_837_; double v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_float_of_nat(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(lean_object* v_cls_842_, lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_ref_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_895_; 
v_ref_849_ = lean_ctor_get(v___y_846_, 2);
v___x_850_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0_spec__0(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_895_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_895_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_895_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v_traceState_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_cache_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_894_; 
v___x_855_ = lean_st_ref_take(v___y_847_);
v_traceState_856_ = lean_ctor_get(v___x_855_, 4);
v_env_857_ = lean_ctor_get(v___x_855_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_855_, 1);
v_ngen_859_ = lean_ctor_get(v___x_855_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_855_, 3);
v_cache_861_ = lean_ctor_get(v___x_855_, 5);
v_messages_862_ = lean_ctor_get(v___x_855_, 6);
v_infoState_863_ = lean_ctor_get(v___x_855_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_855_, 8);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_894_ == 0)
{
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_894_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_cache_861_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_894_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint64_t v_tid_868_; lean_object* v_traces_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_893_; 
v_tid_868_ = lean_ctor_get_uint64(v_traceState_856_, sizeof(void*)*1);
v_traces_869_ = lean_ctor_get(v_traceState_856_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_traceState_856_);
if (v_isSharedCheck_893_ == 0)
{
v___x_871_ = v_traceState_856_;
v_isShared_872_ = v_isSharedCheck_893_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_traces_869_);
lean_dec(v_traceState_856_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_893_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; double v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__0);
v___x_875_ = 0;
v___x_876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__1));
v___x_877_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_877_, 0, v_cls_842_);
lean_ctor_set(v___x_877_, 1, v___x_873_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3, v___x_874_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3 + 8, v___x_874_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 16, v___x_875_);
v___x_878_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___closed__2));
v___x_879_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v_a_851_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
lean_inc(v_ref_849_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_ref_849_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_PersistentArray_push___redArg(v_traces_869_, v___x_880_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_881_);
v___x_883_ = v___x_871_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_881_);
lean_ctor_set_uint64(v_reuseFailAlloc_892_, sizeof(void*)*1, v_tid_868_);
v___x_883_ = v_reuseFailAlloc_892_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_883_);
v___x_885_ = v___x_866_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_env_857_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v_cache_861_);
lean_ctor_set(v_reuseFailAlloc_891_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_891_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_891_, 8, v_snapshotTasks_864_);
v___x_885_ = v_reuseFailAlloc_891_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = lean_st_ref_put(v___y_847_, v___x_885_);
v___x_887_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_887_);
v___x_889_ = v___x_853_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg___boxed(lean_object* v_cls_896_, lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_896_, v_msg_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5(void){
_start:
{
lean_object* v_cls_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_cls_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__4));
v___x_915_ = l_Lean_Name_append(v___x_914_, v_cls_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__6));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(lean_object* v_a_919_, lean_object* v_as_920_, size_t v_i_921_, size_t v_stop_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_eq(v_i_921_, v_stop_922_);
if (v___x_944_ == 0)
{
lean_object* v_toCold_945_; lean_object* v_options_946_; uint8_t v_hasTrace_947_; 
v_toCold_945_ = lean_ctor_get(v___y_934_, 0);
v_options_946_ = lean_ctor_get(v_toCold_945_, 2);
v_hasTrace_947_ = lean_ctor_get_uint8(v_options_946_, sizeof(void*)*1);
if (v_hasTrace_947_ == 0)
{
goto v___jp_942_;
}
else
{
lean_object* v_inheritedTraceOptions_948_; lean_object* v_cls_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_inheritedTraceOptions_948_ = lean_ctor_get(v_toCold_945_, 11);
v_cls_949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_948_, v_options_946_, v___x_950_);
if (v___x_951_ == 0)
{
goto v___jp_942_;
}
else
{
lean_object* v_type_952_; lean_object* v___x_953_; lean_object* v_type_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_type_952_ = lean_ctor_get(v_a_919_, 1);
v___x_953_ = lean_array_uget_borrowed(v_as_920_, v_i_921_);
v_type_954_ = lean_ctor_get(v___x_953_, 1);
lean_inc_ref(v_type_952_);
v___x_955_ = l_Lean_MessageData_ofExpr(v_type_952_);
v___x_956_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
lean_inc_ref(v_type_954_);
v___x_958_ = l_Lean_MessageData_ofExpr(v_type_954_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_949_, v___x_959_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v_a_938_ = v_a_961_;
goto v___jp_937_;
}
else
{
lean_dec_ref(v_a_919_);
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_962_; 
lean_dec_ref(v_a_919_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_b_923_);
return v___x_962_;
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_921_, v___x_939_);
v_i_921_ = v___x_940_;
v_b_923_ = v_a_938_;
goto _start;
}
v___jp_942_:
{
lean_object* v___x_943_; 
v___x_943_ = lean_box(0);
v_a_938_ = v___x_943_;
goto v___jp_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___boxed(lean_object** _args){
lean_object* v_a_963_ = _args[0];
lean_object* v_as_964_ = _args[1];
lean_object* v_i_965_ = _args[2];
lean_object* v_stop_966_ = _args[3];
lean_object* v_b_967_ = _args[4];
lean_object* v___y_968_ = _args[5];
lean_object* v___y_969_ = _args[6];
lean_object* v___y_970_ = _args[7];
lean_object* v___y_971_ = _args[8];
lean_object* v___y_972_ = _args[9];
lean_object* v___y_973_ = _args[10];
lean_object* v___y_974_ = _args[11];
lean_object* v___y_975_ = _args[12];
lean_object* v___y_976_ = _args[13];
lean_object* v___y_977_ = _args[14];
lean_object* v___y_978_ = _args[15];
lean_object* v___y_979_ = _args[16];
lean_object* v___y_980_ = _args[17];
_start:
{
size_t v_i_boxed_981_; size_t v_stop_boxed_982_; lean_object* v_res_983_; 
v_i_boxed_981_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_stop_boxed_982_ = lean_unbox_usize(v_stop_966_);
lean_dec(v_stop_966_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v_a_963_, v_as_964_, v_i_boxed_981_, v_stop_boxed_982_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(lean_object* v_as_986_, size_t v_i_987_, size_t v_stop_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_a_1004_; lean_object* v___y_1010_; uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_eq(v_i_987_, v_stop_988_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
v___x_1015_ = lean_st_mk_ref(v___x_1014_);
v___x_1016_ = lean_array_uget_borrowed(v_as_986_, v_i_987_);
lean_inc(v___x_1016_);
v___x_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_processHyp___redArg(v___x_1016_, v___x_1015_, v___y_990_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v_isZero_1020_; 
lean_dec_ref_known(v___x_1017_, 1);
v___x_1018_ = lean_st_ref_get(v___x_1015_);
lean_dec(v___x_1015_);
v___x_1019_ = lean_array_get_size(v___x_1018_);
v_isZero_1020_ = lean_nat_dec_eq(v___x_1019_, v___x_1013_);
if (v_isZero_1020_ == 1)
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_lt(v___x_1013_, v___x_1019_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v_caches_1023_; lean_object* v_typeAnalysis_1024_; lean_object* v_target_1025_; lean_object* v_hypotheses_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v___x_1022_ = lean_st_ref_take(v___y_992_);
v_caches_1023_ = lean_ctor_get(v___x_1022_, 0);
v_typeAnalysis_1024_ = lean_ctor_get(v___x_1022_, 1);
v_target_1025_ = lean_ctor_get(v___x_1022_, 2);
v_hypotheses_1026_ = lean_ctor_get(v___x_1022_, 3);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1022_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_hypotheses_1026_);
lean_inc(v_target_1025_);
lean_inc(v_typeAnalysis_1024_);
lean_inc(v_caches_1023_);
lean_dec(v___x_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_caches_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_typeAnalysis_1024_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_target_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_hypotheses_1026_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*4, v_isZero_1020_);
v___x_1032_ = lean_st_ref_put(v___y_992_, v___x_1031_);
v_a_1004_ = v___x_1018_;
goto v___jp_1003_;
}
}
}
else
{
lean_object* v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = lean_box(0);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1019_);
lean_inc(v___x_1016_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1016_, v___x_1018_, v___x_1036_, v___x_1037_, v___x_1035_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; lean_object* v_caches_1040_; lean_object* v_typeAnalysis_1041_; lean_object* v_target_1042_; lean_object* v_hypotheses_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref_known(v___x_1038_, 1);
v___x_1039_ = lean_st_ref_take(v___y_992_);
v_caches_1040_ = lean_ctor_get(v___x_1039_, 0);
v_typeAnalysis_1041_ = lean_ctor_get(v___x_1039_, 1);
v_target_1042_ = lean_ctor_get(v___x_1039_, 2);
v_hypotheses_1043_ = lean_ctor_get(v___x_1039_, 3);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1045_ = v___x_1039_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_hypotheses_1043_);
lean_inc(v_target_1042_);
lean_inc(v_typeAnalysis_1041_);
lean_inc(v_caches_1040_);
lean_dec(v___x_1039_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_caches_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_typeAnalysis_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_target_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_hypotheses_1043_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*4, v___x_1021_);
v___x_1049_ = lean_st_ref_put(v___y_992_, v___x_1048_);
v_a_1004_ = v___x_1018_;
goto v___jp_1003_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_b_989_);
v_a_1052_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1038_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1038_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v_one_1060_; lean_object* v_n_1061_; uint8_t v_isZero_1062_; 
v_one_1060_ = lean_unsigned_to_nat(1u);
v_n_1061_ = lean_nat_sub(v___x_1019_, v_one_1060_);
v_isZero_1062_ = lean_nat_dec_eq(v_n_1061_, v___x_1013_);
lean_dec(v_n_1061_);
if (v_isZero_1062_ == 1)
{
lean_object* v_newHyp_1063_; lean_object* v_type_1064_; lean_object* v_type_1065_; uint8_t v___x_1066_; 
v_newHyp_1063_ = lean_array_fget(v___x_1018_, v___x_1013_);
v_type_1064_ = lean_ctor_get(v_newHyp_1063_, 1);
lean_inc_ref(v_type_1064_);
lean_dec(v_newHyp_1063_);
v_type_1065_ = lean_ctor_get(v___x_1016_, 1);
v___x_1066_ = lean_expr_eqv(v_type_1064_, v_type_1065_);
if (v___x_1066_ == 0)
{
lean_object* v_toCold_1067_; lean_object* v_options_1068_; lean_object* v_inheritedTraceOptions_1069_; uint8_t v_hasTrace_1070_; 
v_toCold_1067_ = lean_ctor_get(v___y_1000_, 0);
v_options_1068_ = lean_ctor_get(v_toCold_1067_, 2);
v_inheritedTraceOptions_1069_ = lean_ctor_get(v_toCold_1067_, 11);
v_hasTrace_1070_ = lean_ctor_get_uint8(v_options_1068_, sizeof(void*)*1);
if (v_hasTrace_1070_ == 0)
{
lean_dec_ref(v_type_1064_);
goto v___jp_1071_;
}
else
{
lean_object* v_cls_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_cls_1074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__2));
v___x_1075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__5);
v___x_1076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1069_, v_options_1068_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec_ref(v_type_1064_);
goto v___jp_1071_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_inc_ref(v_type_1065_);
v___x_1077_ = l_Lean_MessageData_ofExpr(v_type_1065_);
v___x_1078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1___closed__7);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_MessageData_ofExpr(v_type_1064_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1074_, v___x_1081_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_1062_, v___x_1018_, v_a_1083_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
v___y_1010_ = v___x_1084_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_b_989_);
v_a_1085_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1082_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1082_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___lam__0(v_isZero_1062_, v___x_1018_, v___x_1072_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
v___y_1010_ = v___x_1073_;
goto v___jp_1009_;
}
}
else
{
lean_dec_ref(v_type_1064_);
v_a_1004_ = v___x_1018_;
goto v___jp_1003_;
}
}
else
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_nat_dec_lt(v___x_1013_, v___x_1019_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v_caches_1095_; lean_object* v_typeAnalysis_1096_; lean_object* v_target_1097_; lean_object* v_hypotheses_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v___x_1094_ = lean_st_ref_take(v___y_992_);
v_caches_1095_ = lean_ctor_get(v___x_1094_, 0);
v_typeAnalysis_1096_ = lean_ctor_get(v___x_1094_, 1);
v_target_1097_ = lean_ctor_get(v___x_1094_, 2);
v_hypotheses_1098_ = lean_ctor_get(v___x_1094_, 3);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v___x_1094_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_hypotheses_1098_);
lean_inc(v_target_1097_);
lean_inc(v_typeAnalysis_1096_);
lean_inc(v_caches_1095_);
lean_dec(v___x_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
uint8_t v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = 1;
if (v_isShared_1101_ == 0)
{
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_caches_1095_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_typeAnalysis_1096_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_target_1097_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_hypotheses_1098_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*4, v___x_1102_);
v___x_1105_ = lean_st_ref_put(v___y_992_, v___x_1104_);
v_a_1004_ = v___x_1018_;
goto v___jp_1003_;
}
}
}
else
{
lean_object* v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = lean_usize_of_nat(v___x_1019_);
lean_inc(v___x_1016_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__1(v___x_1016_, v___x_1018_, v___x_1109_, v___x_1110_, v___x_1108_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; lean_object* v_caches_1113_; lean_object* v_typeAnalysis_1114_; lean_object* v_target_1115_; lean_object* v_hypotheses_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1112_ = lean_st_ref_take(v___y_992_);
v_caches_1113_ = lean_ctor_get(v___x_1112_, 0);
v_typeAnalysis_1114_ = lean_ctor_get(v___x_1112_, 1);
v_target_1115_ = lean_ctor_get(v___x_1112_, 2);
v_hypotheses_1116_ = lean_ctor_get(v___x_1112_, 3);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1118_ = v___x_1112_;
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_hypotheses_1116_);
lean_inc(v_target_1115_);
lean_inc(v_typeAnalysis_1114_);
lean_inc(v_caches_1113_);
lean_dec(v___x_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_caches_1113_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_typeAnalysis_1114_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_target_1115_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_hypotheses_1116_);
v___x_1121_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; 
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*4, v___x_1093_);
v___x_1122_ = lean_st_ref_put(v___y_992_, v___x_1121_);
v_a_1004_ = v___x_1018_;
goto v___jp_1003_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_b_989_);
v_a_1125_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1111_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1111_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v___x_1015_);
lean_dec_ref(v_b_989_);
v_a_1133_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1017_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1017_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_989_);
return v___x_1141_;
}
v___jp_1003_:
{
lean_object* v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; 
v___x_1005_ = l_Array_append___redArg(v_b_989_, v_a_1004_);
lean_dec_ref(v_a_1004_);
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_987_, v___x_1006_);
v_i_987_ = v___x_1007_;
v_b_989_ = v___x_1005_;
goto _start;
}
v___jp_1009_:
{
if (lean_obj_tag(v___y_1010_) == 0)
{
lean_object* v_a_1011_; 
v_a_1011_ = lean_ctor_get(v___y_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___y_1010_, 1);
v_a_1004_ = v_a_1011_;
goto v___jp_1003_;
}
else
{
lean_dec_ref(v_b_989_);
return v___y_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___boxed(lean_object** _args){
lean_object* v_as_1142_ = _args[0];
lean_object* v_i_1143_ = _args[1];
lean_object* v_stop_1144_ = _args[2];
lean_object* v_b_1145_ = _args[3];
lean_object* v___y_1146_ = _args[4];
lean_object* v___y_1147_ = _args[5];
lean_object* v___y_1148_ = _args[6];
lean_object* v___y_1149_ = _args[7];
lean_object* v___y_1150_ = _args[8];
lean_object* v___y_1151_ = _args[9];
lean_object* v___y_1152_ = _args[10];
lean_object* v___y_1153_ = _args[11];
lean_object* v___y_1154_ = _args[12];
lean_object* v___y_1155_ = _args[13];
lean_object* v___y_1156_ = _args[14];
lean_object* v___y_1157_ = _args[15];
lean_object* v___y_1158_ = _args[16];
_start:
{
size_t v_i_boxed_1159_; size_t v_stop_boxed_1160_; lean_object* v_res_1161_; 
v_i_boxed_1159_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_stop_boxed_1160_ = lean_unbox_usize(v_stop_1144_);
lean_dec(v_stop_1144_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_as_1142_, v_i_boxed_1159_, v_stop_boxed_1160_, v_b_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v_as_1142_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_hypotheses_1178_; lean_object* v___x_1179_; lean_object* v_caches_1180_; lean_object* v_typeAnalysis_1181_; lean_object* v_target_1182_; uint8_t v_didChange_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1246_; 
v___x_1177_ = lean_st_ref_get(v___y_1166_);
v_hypotheses_1178_ = lean_ctor_get(v___x_1177_, 3);
lean_inc_ref(v_hypotheses_1178_);
lean_dec(v___x_1177_);
v___x_1179_ = lean_st_ref_take(v___y_1166_);
v_caches_1180_ = lean_ctor_get(v___x_1179_, 0);
v_typeAnalysis_1181_ = lean_ctor_get(v___x_1179_, 1);
v_target_1182_ = lean_ctor_get(v___x_1179_, 2);
v_didChange_1183_ = lean_ctor_get_uint8(v___x_1179_, sizeof(void*)*4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1179_, 3);
lean_dec(v_unused_1247_);
v___x_1185_ = v___x_1179_;
v_isShared_1186_ = v_isSharedCheck_1246_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_target_1182_);
lean_inc(v_typeAnalysis_1181_);
lean_inc(v_caches_1180_);
lean_dec(v___x_1179_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1246_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2___closed__0));
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 3, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_caches_1180_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_typeAnalysis_1181_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_target_1182_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v___x_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1245_, sizeof(void*)*4, v_didChange_1183_);
v___x_1190_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1191_ = lean_st_ref_put(v___y_1166_, v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___closed__0));
v___x_1193_ = lean_array_get_size(v_hypotheses_1178_);
v___x_1194_ = lean_nat_dec_lt(v___x_1187_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v_caches_1196_; lean_object* v_typeAnalysis_1197_; lean_object* v_target_1198_; uint8_t v_didChange_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_hypotheses_1178_);
v___x_1195_ = lean_st_ref_take(v___y_1166_);
v_caches_1196_ = lean_ctor_get(v___x_1195_, 0);
v_typeAnalysis_1197_ = lean_ctor_get(v___x_1195_, 1);
v_target_1198_ = lean_ctor_get(v___x_1195_, 2);
v_didChange_1199_ = lean_ctor_get_uint8(v___x_1195_, sizeof(void*)*4);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1195_, 3);
lean_dec(v_unused_1210_);
v___x_1201_ = v___x_1195_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_target_1198_);
lean_inc(v_typeAnalysis_1197_);
lean_inc(v_caches_1196_);
lean_dec(v___x_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 3, v___x_1192_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_caches_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_typeAnalysis_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_target_1198_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v___x_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*4, v_didChange_1199_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_st_ref_put(v___y_1166_, v___x_1204_);
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1193_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__2(v_hypotheses_1178_, v___x_1211_, v___x_1212_, v___x_1192_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec_ref(v_hypotheses_1178_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1236_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1236_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1236_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v_caches_1219_; lean_object* v_typeAnalysis_1220_; lean_object* v_target_1221_; uint8_t v_didChange_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1234_; 
v___x_1218_ = lean_st_ref_take(v___y_1166_);
v_caches_1219_ = lean_ctor_get(v___x_1218_, 0);
v_typeAnalysis_1220_ = lean_ctor_get(v___x_1218_, 1);
v_target_1221_ = lean_ctor_get(v___x_1218_, 2);
v_didChange_1222_ = lean_ctor_get_uint8(v___x_1218_, sizeof(void*)*4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1218_, 3);
lean_dec(v_unused_1235_);
v___x_1224_ = v___x_1218_;
v_isShared_1225_ = v_isSharedCheck_1234_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_target_1221_);
lean_inc(v_typeAnalysis_1220_);
lean_inc(v_caches_1219_);
lean_dec(v___x_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1234_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v_a_1214_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_caches_1219_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_typeAnalysis_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_target_1221_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_a_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1233_, sizeof(void*)*4, v_didChange_1222_);
v___x_1227_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1228_ = lean_st_ref_put(v___y_1166_, v___x_1227_);
v___x_1229_ = lean_box(0);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1229_);
v___x_1231_ = v___x_1216_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1213_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1213_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0___boxed(lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___lam__0(v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(lean_object* v_g_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___f_1277_; lean_object* v___x_1278_; 
v___f_1277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___closed__0));
v___x_1278_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__3___redArg(v_g_1263_, v___f_1277_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process___boxed(lean_object* v_g_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v_g_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(lean_object* v_cls_1294_, lean_object* v_msg_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___redArg(v_cls_1294_, v_msg_1295_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0___boxed(lean_object* v_cls_1310_, lean_object* v_msg_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process_spec__0(v_cls_1310_, v_msg_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
return v_res_1325_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_unsigned_to_nat(16u);
v___x_1328_ = lean_mk_array(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__0);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v_target_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = lean_st_ref_get(v___y_1333_);
v_target_1345_ = lean_ctor_get(v___x_1344_, 2);
lean_inc_ref(v_target_1345_);
lean_dec(v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___closed__1);
v___x_1347_ = lean_st_mk_ref(v___x_1346_);
v___x_1348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1345_);
lean_dec_ref(v_target_1345_);
v___x_1349_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten_0__Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass_process(v___x_1348_, v___x_1347_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v___x_1349_, 0);
lean_dec(v_unused_1360_);
v___x_1351_ = v___x_1349_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v___x_1349_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1353_ = lean_st_ref_get(v___x_1347_);
lean_dec(v___x_1347_);
lean_dec(v___x_1353_);
v___x_1354_ = 0;
v___x_1355_ = lean_box(v___x_1354_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1355_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v___x_1347_);
v_a_1361_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1349_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0___boxed(lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass___lam__0(v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1381_;
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
