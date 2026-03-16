// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.EmbeddedConstraint
// Imports: public import Std.Tactic.BVDecide.Normalize.Bool public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2___boxed, .m_arity = 9, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "embeddedConstraintSubstitution"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 224, 35, 207, 121, 34, 254, 217)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___closed__4_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_7(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0(v_x_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object* v_mvarId_19_, lean_object* v_x_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_28_, 0, v_x_20_);
lean_closure_set(v___f_28_, 1, v___y_21_);
lean_closure_set(v___f_28_, 2, v___y_22_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_19_, v___f_28_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object* v_mvarId_38_, lean_object* v_x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_38_, v_x_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_getPropHyps(v___y_72_, v___y_73_, v___y_74_, v___y_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__0(v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
return v_x_86_;
}
else
{
lean_object* v_key_88_; lean_object* v_value_89_; lean_object* v_tail_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_113_; 
v_key_88_ = lean_ctor_get(v_x_87_, 0);
v_value_89_ = lean_ctor_get(v_x_87_, 1);
v_tail_90_ = lean_ctor_get(v_x_87_, 2);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_113_ == 0)
{
v___x_92_ = v_x_87_;
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_tail_90_);
lean_inc(v_value_89_);
lean_inc(v_key_88_);
lean_dec(v_x_87_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v_fold_98_; uint64_t v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; size_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_94_ = lean_array_get_size(v_x_86_);
v___x_95_ = l_Lean_Expr_hash(v_key_88_);
v___x_96_ = 32ULL;
v___x_97_ = lean_uint64_shift_right(v___x_95_, v___x_96_);
v_fold_98_ = lean_uint64_xor(v___x_95_, v___x_97_);
v___x_99_ = 16ULL;
v___x_100_ = lean_uint64_shift_right(v_fold_98_, v___x_99_);
v___x_101_ = lean_uint64_xor(v_fold_98_, v___x_100_);
v___x_102_ = lean_uint64_to_usize(v___x_101_);
v___x_103_ = lean_usize_of_nat(v___x_94_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_sub(v___x_103_, v___x_104_);
v___x_106_ = lean_usize_land(v___x_102_, v___x_105_);
v___x_107_ = lean_array_uget_borrowed(v_x_86_, v___x_106_);
lean_inc(v___x_107_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v___x_107_);
v___x_109_ = v___x_92_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_key_88_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_value_89_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v___x_107_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_array_uset(v_x_86_, v___x_106_, v___x_109_);
v_x_86_ = v___x_110_;
v_x_87_ = v_tail_90_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_114_, lean_object* v_source_115_, lean_object* v_target_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_array_get_size(v_source_115_);
v___x_118_ = lean_nat_dec_lt(v_i_114_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec_ref(v_source_115_);
lean_dec(v_i_114_);
return v_target_116_;
}
else
{
lean_object* v_es_119_; lean_object* v___x_120_; lean_object* v_source_121_; lean_object* v_target_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_es_119_ = lean_array_fget(v_source_115_, v_i_114_);
v___x_120_ = lean_box(0);
v_source_121_ = lean_array_fset(v_source_115_, v_i_114_, v___x_120_);
v_target_122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_target_116_, v_es_119_);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_i_114_, v___x_123_);
lean_dec(v_i_114_);
v_i_114_ = v___x_124_;
v_source_115_ = v_source_121_;
v_target_116_ = v_target_122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(lean_object* v_data_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_nbuckets_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_127_ = lean_array_get_size(v_data_126_);
v___x_128_ = lean_unsigned_to_nat(2u);
v_nbuckets_129_ = lean_nat_mul(v___x_127_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_box(0);
v___x_132_ = lean_mk_array(v_nbuckets_129_, v___x_131_);
v___x_133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v___x_130_, v_data_126_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(lean_object* v_a_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
else
{
lean_object* v_key_137_; lean_object* v_tail_138_; uint8_t v___x_139_; 
v_key_137_ = lean_ctor_get(v_x_135_, 0);
v_tail_138_ = lean_ctor_get(v_x_135_, 2);
v___x_139_ = lean_expr_eqv(v_key_137_, v_a_134_);
if (v___x_139_ == 0)
{
v_x_135_ = v_tail_138_;
goto _start;
}
else
{
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg___boxed(lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_141_, v_x_142_);
lean_dec(v_x_142_);
lean_dec_ref(v_a_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object* v_m_145_, lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_size_148_; lean_object* v_buckets_149_; lean_object* v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_fold_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v_bkt_163_; uint8_t v___x_164_; 
v_size_148_ = lean_ctor_get(v_m_145_, 0);
v_buckets_149_ = lean_ctor_get(v_m_145_, 1);
v___x_150_ = lean_array_get_size(v_buckets_149_);
v___x_151_ = l_Lean_Expr_hash(v_a_146_);
v___x_152_ = 32ULL;
v___x_153_ = lean_uint64_shift_right(v___x_151_, v___x_152_);
v_fold_154_ = lean_uint64_xor(v___x_151_, v___x_153_);
v___x_155_ = 16ULL;
v___x_156_ = lean_uint64_shift_right(v_fold_154_, v___x_155_);
v___x_157_ = lean_uint64_xor(v_fold_154_, v___x_156_);
v___x_158_ = lean_uint64_to_usize(v___x_157_);
v___x_159_ = lean_usize_of_nat(v___x_150_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_sub(v___x_159_, v___x_160_);
v___x_162_ = lean_usize_land(v___x_158_, v___x_161_);
v_bkt_163_ = lean_array_uget_borrowed(v_buckets_149_, v___x_162_);
v___x_164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_146_, v_bkt_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_185_; 
lean_inc_ref(v_buckets_149_);
lean_inc(v_size_148_);
v_isSharedCheck_185_ = !lean_is_exclusive(v_m_145_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_186_ = lean_ctor_get(v_m_145_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_m_145_, 0);
lean_dec(v_unused_187_);
v___x_166_ = v_m_145_;
v_isShared_167_ = v_isSharedCheck_185_;
goto v_resetjp_165_;
}
else
{
lean_dec(v_m_145_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_185_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v_size_x27_169_; lean_object* v___x_170_; lean_object* v_buckets_x27_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_168_ = lean_unsigned_to_nat(1u);
v_size_x27_169_ = lean_nat_add(v_size_148_, v___x_168_);
lean_dec(v_size_148_);
lean_inc(v_bkt_163_);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v_a_146_);
lean_ctor_set(v___x_170_, 1, v_b_147_);
lean_ctor_set(v___x_170_, 2, v_bkt_163_);
v_buckets_x27_171_ = lean_array_uset(v_buckets_149_, v___x_162_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(4u);
v___x_173_ = lean_nat_mul(v_size_x27_169_, v___x_172_);
v___x_174_ = lean_unsigned_to_nat(3u);
v___x_175_ = lean_nat_div(v___x_173_, v___x_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_array_get_size(v_buckets_x27_171_);
v___x_177_ = lean_nat_dec_le(v___x_175_, v___x_176_);
lean_dec(v___x_175_);
if (v___x_177_ == 0)
{
lean_object* v_val_178_; lean_object* v___x_180_; 
v_val_178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_buckets_x27_171_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_val_178_);
lean_ctor_set(v___x_166_, 0, v_size_x27_169_);
v___x_180_ = v___x_166_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_size_x27_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_val_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_183_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_buckets_x27_171_);
lean_ctor_set(v___x_166_, 0, v_size_x27_169_);
v___x_183_ = v___x_166_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_size_x27_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_buckets_x27_171_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_dec(v_b_147_);
lean_dec_ref(v_a_146_);
return v_m_145_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg(lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_buckets_190_; lean_object* v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v_fold_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_buckets_190_ = lean_ctor_get(v_m_188_, 1);
v___x_191_ = lean_array_get_size(v_buckets_190_);
v___x_192_ = l_Lean_Expr_hash(v_a_189_);
v___x_193_ = 32ULL;
v___x_194_ = lean_uint64_shift_right(v___x_192_, v___x_193_);
v_fold_195_ = lean_uint64_xor(v___x_192_, v___x_194_);
v___x_196_ = 16ULL;
v___x_197_ = lean_uint64_shift_right(v_fold_195_, v___x_196_);
v___x_198_ = lean_uint64_xor(v_fold_195_, v___x_197_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = lean_usize_of_nat(v___x_191_);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_sub(v___x_200_, v___x_201_);
v___x_203_ = lean_usize_land(v___x_199_, v___x_202_);
v___x_204_ = lean_array_uget_borrowed(v_buckets_190_, v___x_203_);
v___x_205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_189_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_206_, v_a_207_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_m_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object* v_as_218_, size_t v_sz_219_, size_t v_i_220_, lean_object* v_b_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_a_228_; uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_lt(v_i_220_, v_sz_219_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_b_221_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_array_uget_borrowed(v_as_218_, v_i_220_);
lean_inc_ref(v___y_222_);
lean_inc(v_a_234_);
v___x_235_ = l_Lean_FVarId_getType___redArg(v_a_234_, v___y_222_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_snd_236_; lean_object* v_a_237_; lean_object* v_fst_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_302_; 
v_snd_236_ = lean_ctor_get(v_b_221_, 1);
lean_inc(v_snd_236_);
v_a_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_235_);
v_fst_238_ = lean_ctor_get(v_b_221_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_b_221_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_b_221_, 1);
lean_dec(v_unused_303_);
v___x_240_ = v_b_221_;
v_isShared_241_ = v_isSharedCheck_302_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_fst_238_);
lean_dec(v_b_221_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_302_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_301_; 
v_fst_242_ = lean_ctor_get(v_snd_236_, 0);
v_snd_243_ = lean_ctor_get(v_snd_236_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_snd_236_);
if (v_isSharedCheck_301_ == 0)
{
v___x_245_ = v_snd_236_;
v_isShared_246_ = v_isSharedCheck_301_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
lean_dec(v_snd_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_301_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = l_Lean_Expr_cleanupAnnotations(v_a_237_);
v___x_255_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_255_ == 0)
{
lean_dec_ref(v___x_254_);
goto v___jp_247_;
}
else
{
lean_object* v_arg_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_arg_256_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_arg_256_);
v___x_257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
v___x_258_ = l_Lean_Expr_isApp(v___x_257_);
if (v___x_258_ == 0)
{
lean_dec_ref(v___x_257_);
lean_dec_ref(v_arg_256_);
goto v___jp_247_;
}
else
{
lean_object* v_arg_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_arg_259_ = lean_ctor_get(v___x_257_, 1);
lean_inc_ref(v_arg_259_);
v___x_260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_257_);
v___x_261_ = l_Lean_Expr_isApp(v___x_260_);
if (v___x_261_ == 0)
{
lean_dec_ref(v___x_260_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_256_);
goto v___jp_247_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_260_);
v___x_263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__1));
v___x_264_ = l_Lean_Expr_isConstOf(v___x_262_, v___x_263_);
lean_dec_ref(v___x_262_);
if (v___x_264_ == 0)
{
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_256_);
goto v___jp_247_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
lean_del_object(v___x_245_);
lean_del_object(v___x_240_);
v___x_265_ = l_Lean_Expr_cleanupAnnotations(v_arg_256_);
v___x_266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___closed__4));
v___x_267_ = l_Lean_Expr_isConstOf(v___x_265_, v___x_266_);
lean_dec_ref(v___x_265_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_arg_259_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_fst_242_);
lean_ctor_set(v___x_268_, 1, v_snd_243_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v_fst_238_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v_a_228_ = v___x_269_;
goto v___jp_227_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg(v_fst_242_, v_arg_259_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_inc_ref(v___y_222_);
lean_inc(v_a_234_);
v___x_271_ = l_Lean_FVarId_getDecl___redArg(v_a_234_, v___y_222_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
v___x_273_ = l_Lean_LocalDecl_toExpr(v_a_272_);
lean_inc(v_a_234_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_a_234_);
v___x_275_ = l_Lean_Meta_simpGlobalConfig;
lean_inc(v___y_225_);
lean_inc_ref(v___y_224_);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
v___x_276_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_fst_238_, v___x_274_, v___x_273_, v___x_275_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = lean_box(0);
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1___redArg(v_fst_242_, v_arg_259_, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_snd_243_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_277_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v_a_228_ = v___x_281_;
goto v___jp_227_;
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_arg_259_);
lean_dec(v_snd_243_);
lean_dec(v_fst_242_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v_a_282_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_276_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_276_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_arg_259_);
lean_dec(v_snd_243_);
lean_dec(v_fst_242_);
lean_dec(v_fst_238_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
v_a_290_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_271_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_271_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_arg_259_);
lean_inc(v_a_234_);
v___x_298_ = lean_array_push(v_snd_243_, v_a_234_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_fst_242_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_fst_238_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v_a_228_ = v___x_300_;
goto v___jp_227_;
}
}
}
}
}
}
v___jp_247_:
{
lean_object* v___x_249_; 
if (v_isShared_246_ == 0)
{
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_fst_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_243_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_249_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_fst_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v_a_228_ = v___x_251_;
goto v___jp_227_;
}
}
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec_ref(v_b_221_);
v_a_304_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_235_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_235_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
v___jp_227_:
{
size_t v___x_229_; size_t v___x_230_; 
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_220_, v___x_229_);
v_i_220_ = v___x_230_;
v_b_221_ = v_a_228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object* v_as_312_, lean_object* v_sz_313_, lean_object* v_i_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
size_t v_sz_boxed_321_; size_t v_i_boxed_322_; lean_object* v_res_323_; 
v_sz_boxed_321_ = lean_unbox_usize(v_sz_313_);
lean_dec(v_sz_313_);
v_i_boxed_322_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_312_, v_sz_boxed_321_, v_i_boxed_322_, v_b_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec_ref(v_as_312_);
return v_res_323_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_unsigned_to_nat(16u);
v___x_328_ = lean_mk_array(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_seen_331_; 
v___x_329_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__1);
v___x_330_ = lean_unsigned_to_nat(0u);
v_seen_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_seen_331_, 0, v___x_330_);
lean_ctor_set(v_seen_331_, 1, v___x_329_);
return v_seen_331_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3(void){
_start:
{
lean_object* v_relevantHyps_332_; lean_object* v_seen_333_; lean_object* v___x_334_; 
v_relevantHyps_332_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0));
v_seen_333_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__2);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_seen_333_);
lean_ctor_set(v___x_334_, 1, v_relevantHyps_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v_relevantHyps_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__3);
v_relevantHyps_336_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0));
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v_relevantHyps_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__5);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_unsigned_to_nat(32u);
v___x_345_ = lean_mk_empty_array_with_capacity(v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9(void){
_start:
{
size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_347_ = ((size_t)5ULL);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_unsigned_to_nat(32u);
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_349_);
v___x_351_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__8);
v___x_352_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_348_);
lean_ctor_set(v___x_352_, 3, v___x_348_);
lean_ctor_set_usize(v___x_352_, 4, v___x_347_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__9);
v___x_354_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__6);
v___x_355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set(v___x_355_, 3, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__10);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__7);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1(lean_object* v_goal_359_, lean_object* v___f_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
v___x_368_ = l_Lean_Meta_getPropHyps(v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v_relevantHyps_371_; lean_object* v___x_372_; size_t v_sz_373_; size_t v___x_374_; lean_object* v___x_375_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v___x_370_ = lean_unsigned_to_nat(0u);
v_relevantHyps_371_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__0));
v___x_372_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__4);
v_sz_373_ = lean_array_size(v_a_369_);
v___x_374_ = ((size_t)0ULL);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg(v_a_369_, v_sz_373_, v___x_374_, v___x_372_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v_a_369_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v_snd_377_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_380_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
v_snd_377_ = lean_ctor_get(v_a_376_, 1);
lean_inc(v_snd_377_);
v_fst_378_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_fst_378_);
lean_dec(v_a_376_);
v_snd_379_ = lean_ctor_get(v_snd_377_, 1);
lean_inc(v_snd_379_);
lean_dec(v_snd_377_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
v___x_380_ = l_Lean_MVarId_tryClearMany(v_goal_359_, v_snd_379_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v_snd_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_458_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_458_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_458_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_458_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_array_get_size(v_fst_378_);
v___x_386_ = lean_nat_dec_eq(v___x_385_, v___x_370_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_del_object(v___x_383_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc_ref(v___y_361_);
lean_inc(v_a_381_);
v___x_387_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(v_a_381_, v___f_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
v___x_389_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_366_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_maxSteps_391_; uint8_t v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref(v___x_389_);
v_maxSteps_391_ = lean_ctor_get(v___y_361_, 1);
lean_inc(v_maxSteps_391_);
lean_dec_ref(v___y_361_);
v___x_392_ = 1;
v___x_393_ = lean_unsigned_to_nat(2u);
v___x_394_ = 0;
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_396_, 0, v_maxSteps_391_);
lean_ctor_set(v___x_396_, 1, v___x_393_);
lean_ctor_set(v___x_396_, 2, v___x_395_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 1, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 2, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 3, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 4, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 5, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 6, v___x_394_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 7, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 8, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 9, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 10, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 11, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 12, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 13, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 14, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 15, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 16, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 17, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 18, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 19, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 20, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 21, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 22, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 23, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 24, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 25, v___x_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 26, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 27, v___x_386_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 28, v___x_392_);
v___x_397_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_396_, v_fst_378_, v_a_390_, v___y_363_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___closed__11);
v___x_400_ = l_Lean_Meta_simpGoal(v_a_381_, v_a_398_, v_relevantHyps_371_, v___x_395_, v___x_392_, v_a_388_, v___x_399_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_421_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_421_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_421_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_421_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_fst_405_; 
v_fst_405_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_fst_405_);
lean_dec(v_a_401_);
if (lean_obj_tag(v_fst_405_) == 1)
{
lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_417_; 
v_val_406_ = lean_ctor_get(v_fst_405_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_fst_405_);
if (v_isSharedCheck_417_ == 0)
{
v___x_408_ = v_fst_405_;
v_isShared_409_ = v_isSharedCheck_417_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v_fst_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_417_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_snd_410_; lean_object* v___x_412_; 
v_snd_410_ = lean_ctor_get(v_val_406_, 1);
lean_inc(v_snd_410_);
lean_dec(v_val_406_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v_snd_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_snd_410_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_412_);
v___x_414_ = v___x_403_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v_fst_405_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_395_);
v___x_419_ = v___x_403_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_395_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_400_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_400_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_a_388_);
lean_dec(v_a_381_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
v_a_430_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_397_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_397_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_a_388_);
lean_dec(v_a_381_);
lean_dec(v_fst_378_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___y_361_);
v_a_438_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_389_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_389_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_381_);
lean_dec(v_fst_378_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v___y_361_);
v_a_446_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_387_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_387_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec(v_fst_378_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___f_360_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_a_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_454_);
v___x_456_ = v___x_383_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
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
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_fst_378_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___f_360_);
v_a_459_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_380_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_380_);
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
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___f_360_);
lean_dec(v_goal_359_);
v_a_467_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_375_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_375_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___f_360_);
lean_dec(v_goal_359_);
v_a_475_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_368_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_368_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v_goal_483_, lean_object* v___f_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1(v_goal_483_, v___f_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2(lean_object* v___f_493_, lean_object* v_goal_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___f_502_; lean_object* v___x_503_; 
lean_inc(v_goal_494_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__1___boxed), 9, 2);
lean_closure_set(v___f_502_, 0, v_goal_494_);
lean_closure_set(v___f_502_, 1, v___f_493_);
v___x_503_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__3___redArg(v_goal_494_, v___f_502_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2___boxed(lean_object* v___f_504_, lean_object* v_goal_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass___lam__2(v___f_504_, v_goal_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v_res_513_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0(lean_object* v_00_u03b2_524_, lean_object* v_m_525_, lean_object* v_a_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___redArg(v_m_525_, v_a_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0___boxed(lean_object* v_00_u03b2_528_, lean_object* v_m_529_, lean_object* v_a_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0(v_00_u03b2_528_, v_m_529_, v_a_530_);
lean_dec_ref(v_a_530_);
lean_dec_ref(v_m_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1(lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1___redArg(v_m_534_, v_a_535_, v_b_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2(lean_object* v_as_538_, size_t v_sz_539_, size_t v_i_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___redArg(v_as_538_, v_sz_539_, v_i_540_, v_b_541_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_as_550_, lean_object* v_sz_551_, lean_object* v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_551_);
lean_dec(v_sz_551_);
v_i_boxed_562_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__2(v_as_550_, v_sz_boxed_561_, v_i_boxed_562_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v_as_550_);
return v_res_563_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0(lean_object* v_00_u03b2_564_, lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___redArg(v_a_565_, v_x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_568_, lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__0_spec__0(v_00_u03b2_568_, v_a_569_, v_x_570_);
lean_dec(v_x_570_);
lean_dec_ref(v_a_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2(lean_object* v_00_u03b2_573_, lean_object* v_data_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2___redArg(v_data_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_576_, lean_object* v_i_577_, lean_object* v_source_578_, lean_object* v_target_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4___redArg(v_i_577_, v_source_578_, v_target_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_embeddedConstraintPass_spec__1_spec__2_spec__4_spec__6___redArg(v_x_582_, v_x_583_);
return v___x_584_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_EmbeddedConstraint(builtin);
}
#ifdef __cplusplus
}
#endif
