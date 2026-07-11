// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "intToBitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 217, 71, 86, 75, 235, 18, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_relevantTerms_7_; lean_object* v_relevantHyps_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v___x_6_ = lean_st_ref_take(v_a_4_);
v_relevantTerms_7_ = lean_ctor_get(v___x_6_, 0);
v_relevantHyps_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_relevantHyps_8_);
lean_inc(v_relevantTerms_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_12_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_13_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_14_ = lean_box(0);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_12_, v___x_13_, v_relevantTerms_7_, v_e_3_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_relevantHyps_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_st_ref_set(v_a_4_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_14_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(v_e_22_, v_a_23_);
lean_dec(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_relevantTerms_34_; lean_object* v_relevantHyps_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_48_; 
v___x_33_ = lean_st_ref_take(v_a_27_);
v_relevantTerms_34_ = lean_ctor_get(v___x_33_, 0);
v_relevantHyps_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_48_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_relevantHyps_35_);
lean_inc(v_relevantTerms_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_41_ = lean_box(0);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_39_, v___x_40_, v_relevantTerms_34_, v_e_26_, v___x_41_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_42_);
v___x_44_ = v___x_37_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_relevantHyps_35_);
v___x_44_ = v_reuseFailAlloc_47_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_st_ref_set(v_a_27_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_41_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_relevantTerms_63_; lean_object* v_relevantHyps_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v___x_62_ = lean_st_ref_take(v_a_60_);
v_relevantTerms_63_ = lean_ctor_get(v___x_62_, 0);
v_relevantHyps_64_ = lean_ctor_get(v___x_62_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_66_ = v___x_62_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_relevantHyps_64_);
lean_inc(v_relevantTerms_63_);
lean_dec(v___x_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_70_ = lean_box(0);
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_68_, v___x_69_, v_relevantHyps_64_, v_f_59_, v___x_70_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_relevantTerms_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_set(v_a_60_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_relevantTerms_90_; lean_object* v_relevantHyps_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v___x_89_ = lean_st_ref_take(v_a_83_);
v_relevantTerms_90_ = lean_ctor_get(v___x_89_, 0);
v_relevantHyps_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_104_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_relevantHyps_91_);
lean_inc(v_relevantTerms_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_95_, v___x_96_, v_relevantHyps_91_, v_f_82_, v___x_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_relevantTerms_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_st_ref_set(v_a_83_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(v_f_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object* v_e_113_, lean_object* v___y_114_){
_start:
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_Expr_hasMVar(v_e_113_);
v___x_117_ = lean_bool_not(v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v_mctx_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_123_; lean_object* v_cache_124_; lean_object* v_zetaDeltaFVarIds_125_; lean_object* v_postponed_126_; lean_object* v_diag_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_136_; 
v___x_118_ = lean_st_ref_get(v___y_114_);
v_mctx_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_mctx_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_instantiateMVarsCore(v_mctx_119_, v_e_113_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_st_ref_take(v___y_114_);
v_cache_124_ = lean_ctor_get(v___x_123_, 1);
v_zetaDeltaFVarIds_125_ = lean_ctor_get(v___x_123_, 2);
v_postponed_126_ = lean_ctor_get(v___x_123_, 3);
v_diag_127_ = lean_ctor_get(v___x_123_, 4);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_137_);
v___x_129_ = v___x_123_;
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_diag_127_);
lean_inc(v_postponed_126_);
lean_inc(v_zetaDeltaFVarIds_125_);
lean_inc(v_cache_124_);
lean_dec(v___x_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_snd_122_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_snd_122_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_cache_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_zetaDeltaFVarIds_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_postponed_126_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_diag_127_);
v___x_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_st_ref_set(v___y_114_, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_fst_121_);
return v___x_134_;
}
}
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_e_113_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_e_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_139_, v___y_140_);
lean_dec(v___y_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object* v_e_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_143_, v___y_145_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object* v_e_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object* v_mvarId_157_, lean_object* v_x_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_157_, v_x_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_164_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_164_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object* v_mvarId_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object* v_00_u03b1_189_, lean_object* v_mvarId_190_, lean_object* v_x_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_190_, v_x_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object* v_00_u03b1_198_, lean_object* v_mvarId_199_, lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_198_, v_mvarId_199_, v_x_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = l_Lean_Level_ofNat(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v___x_227_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9);
v___x_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10);
v___x_230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
v___x_231_ = l_Lean_mkConst(v___x_230_, v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object* v_as_237_, size_t v_sz_238_, size_t v_i_239_, lean_object* v_b_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v_b_240_);
return v___x_247_;
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; 
lean_dec_ref(v_b_240_);
v_a_248_ = lean_array_uget_borrowed(v_as_237_, v_i_239_);
lean_inc(v_a_248_);
v___x_249_ = l_Lean_FVarId_getType___redArg(v_a_248_, v___y_241_, v___y_243_, v___y_244_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_250_, v___y_242_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_252_, v___y_242_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_a_256_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v___x_262_ = l_Lean_Expr_cleanupAnnotations(v_a_254_);
v___x_263_ = l_Lean_Expr_isApp(v___x_262_);
if (v___x_263_ == 0)
{
lean_dec_ref(v___x_262_);
v_a_256_ = v___x_261_;
goto v___jp_255_;
}
else
{
lean_object* v_arg_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_arg_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc_ref(v_arg_264_);
v___x_265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_262_);
v___x_266_ = l_Lean_Expr_isApp(v___x_265_);
if (v___x_266_ == 0)
{
lean_dec_ref(v___x_265_);
lean_dec_ref(v_arg_264_);
v_a_256_ = v___x_261_;
goto v___jp_255_;
}
else
{
lean_object* v_arg_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_arg_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc_ref(v_arg_267_);
v___x_268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_265_);
v___x_269_ = l_Lean_Expr_isApp(v___x_268_);
if (v___x_269_ == 0)
{
lean_dec_ref(v___x_268_);
lean_dec_ref(v_arg_267_);
lean_dec_ref(v_arg_264_);
v_a_256_ = v___x_261_;
goto v___jp_255_;
}
else
{
lean_object* v_arg_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_arg_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc_ref(v_arg_270_);
v___x_271_ = l_Lean_Expr_appFnCleanup___redArg(v___x_268_);
v___x_272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_273_ = l_Lean_Expr_isConstOf(v___x_271_, v___x_272_);
lean_dec_ref(v___x_271_);
if (v___x_273_ == 0)
{
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_267_);
lean_dec_ref(v_arg_264_);
v_a_256_ = v___x_261_;
goto v___jp_255_;
}
else
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_275_ = l_Lean_Expr_isConstOf(v_arg_267_, v___x_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Expr_isConstOf(v_arg_264_, v___x_274_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_267_);
lean_dec_ref(v_arg_264_);
v_a_256_ = v___x_261_;
goto v___jp_255_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_getNatValue_x3f(v_arg_267_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_303_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_303_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
if (lean_obj_tag(v_a_278_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_298_; 
v_val_282_ = lean_ctor_get(v_a_278_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_298_ == 0)
{
v___x_284_ = v_a_278_;
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v_a_278_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_286_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
lean_inc(v_a_248_);
v___x_287_ = l_Lean_mkFVar(v_a_248_);
v___x_288_ = l_Lean_mkApp4(v___x_286_, v_arg_270_, v_arg_267_, v_arg_264_, v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_val_282_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_289_);
v___x_291_ = v___x_284_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_297_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_260_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_293_);
v___x_295_ = v___x_280_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
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
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_dec(v_a_278_);
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_267_);
lean_dec_ref(v_arg_264_);
v___x_299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13));
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_299_);
v___x_301_ = v___x_280_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_267_);
lean_dec_ref(v_arg_264_);
v_a_304_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_277_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_277_);
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
}
else
{
lean_object* v___x_312_; 
lean_dec_ref(v_arg_270_);
lean_dec_ref(v_arg_267_);
v___x_312_ = l_Lean_Meta_getNatValue_x3f(v_arg_264_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec_ref(v_arg_264_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_336_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_336_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
if (lean_obj_tag(v_a_313_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_331_; 
v_val_317_ = lean_ctor_get(v_a_313_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_313_);
if (v_isSharedCheck_331_ == 0)
{
v___x_319_ = v_a_313_;
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_dec(v_a_313_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_a_248_);
v___x_321_ = l_Lean_mkFVar(v_a_248_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_val_317_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_322_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_330_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_260_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_326_);
v___x_328_ = v___x_315_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v_a_313_);
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13));
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_332_);
v___x_334_ = v___x_315_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_312_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_312_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
}
v___jp_255_:
{
size_t v___x_257_; size_t v___x_258_; 
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_add(v_i_239_, v___x_257_);
lean_inc_ref(v_a_256_);
v_i_239_ = v___x_258_;
v_b_240_ = v_a_256_;
goto _start;
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_253_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_253_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_251_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_251_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_249_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_249_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object* v_as_369_, lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_b_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
size_t v_sz_boxed_378_; size_t v_i_boxed_379_; lean_object* v_res_380_; 
v_sz_boxed_378_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_379_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_369_, v_sz_boxed_378_, v_i_boxed_379_, v_b_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v_as_369_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_getPropHyps(v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; size_t v_sz_390_; size_t v___x_391_; lean_object* v___x_392_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = lean_box(0);
v___x_389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v_sz_390_ = lean_array_size(v_a_387_);
v___x_391_ = ((size_t)0ULL);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_387_, v_sz_390_, v___x_391_, v___x_389_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v_a_387_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_fst_397_; 
v_fst_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_fst_397_);
lean_dec(v_a_393_);
if (lean_obj_tag(v_fst_397_) == 0)
{
lean_object* v___x_399_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_388_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_388_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v_val_401_; lean_object* v___x_403_; 
v_val_401_ = lean_ctor_get(v_fst_397_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_fst_397_, 1);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_val_401_);
v___x_403_ = v___x_395_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_val_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_a_406_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_392_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_392_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_414_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_386_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_386_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(lean_object* v_goal_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; 
v___f_435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0));
v___x_436_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_429_, v___f_435_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object* v_goal_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(lean_object* v_e_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = l_Lean_Expr_hasMVar(v_e_444_);
v___x_448_ = lean_bool_not(v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; lean_object* v_cache_455_; lean_object* v_zetaDeltaFVarIds_456_; lean_object* v_postponed_457_; lean_object* v_diag_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v___x_449_ = lean_st_ref_get(v___y_445_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_mctx_450_);
lean_dec(v___x_449_);
v___x_451_ = l_Lean_instantiateMVarsCore(v_mctx_450_, v_e_444_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_snd_453_);
lean_dec_ref(v___x_451_);
v___x_454_ = lean_st_ref_take(v___y_445_);
v_cache_455_ = lean_ctor_get(v___x_454_, 1);
v_zetaDeltaFVarIds_456_ = lean_ctor_get(v___x_454_, 2);
v_postponed_457_ = lean_ctor_get(v___x_454_, 3);
v_diag_458_ = lean_ctor_get(v___x_454_, 4);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_468_);
v___x_460_ = v___x_454_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_diag_458_);
lean_inc(v_postponed_457_);
lean_inc(v_zetaDeltaFVarIds_456_);
lean_inc(v_cache_455_);
lean_dec(v___x_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v_snd_453_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_snd_453_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_cache_455_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_zetaDeltaFVarIds_456_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_postponed_457_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_diag_458_);
v___x_463_ = v_reuseFailAlloc_466_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_st_ref_set(v___y_445_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_fst_452_);
return v___x_465_;
}
}
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_e_444_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg___boxed(lean_object* v_e_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_e_470_, v___y_471_);
lean_dec(v___y_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0(lean_object* v_e_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_e_474_, v___y_479_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___boxed(lean_object* v_e_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0(v_e_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object* v_fst_494_, lean_object* v_snd_495_, lean_object* v_prop_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_564_; 
v___x_505_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_prop_496_, v___y_501_);
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_564_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_564_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_564_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = l_Lean_Expr_cleanupAnnotations(v_a_506_);
v___x_516_ = l_Lean_Expr_isApp(v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v___x_515_);
lean_dec_ref(v_snd_495_);
goto v___jp_510_;
}
else
{
lean_object* v_arg_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_arg_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc_ref(v_arg_517_);
v___x_518_ = l_Lean_Expr_appFnCleanup___redArg(v___x_515_);
v___x_519_ = l_Lean_Expr_isApp(v___x_518_);
if (v___x_519_ == 0)
{
lean_dec_ref(v___x_518_);
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_snd_495_);
goto v___jp_510_;
}
else
{
lean_object* v_arg_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_arg_520_ = lean_ctor_get(v___x_518_, 1);
lean_inc_ref(v_arg_520_);
v___x_521_ = l_Lean_Expr_appFnCleanup___redArg(v___x_518_);
v___x_522_ = l_Lean_Expr_isApp(v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v___x_521_);
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_snd_495_);
goto v___jp_510_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = l_Lean_Expr_appFnCleanup___redArg(v___x_521_);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_525_ = l_Lean_Expr_isConstOf(v___x_523_, v___x_524_);
lean_dec_ref(v___x_523_);
if (v___x_525_ == 0)
{
lean_dec_ref(v_arg_520_);
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_snd_495_);
goto v___jp_510_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
lean_del_object(v___x_508_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_527_ = l_Lean_Expr_isConstOf(v_arg_520_, v___x_526_);
lean_dec_ref(v_arg_520_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_snd_495_);
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_getNatValue_x3f(v_arg_517_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec_ref(v_arg_517_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_555_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_555_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
if (lean_obj_tag(v_a_531_) == 1)
{
lean_object* v_val_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_550_; 
v_val_535_ = lean_ctor_get(v_a_531_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_550_ == 0)
{
v___x_537_ = v_a_531_;
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_val_535_);
lean_dec(v_a_531_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_nat_dec_eq(v_fst_494_, v_val_535_);
lean_dec(v_val_535_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_542_; 
lean_del_object(v___x_537_);
lean_dec_ref(v_snd_495_);
v___x_540_ = lean_box(0);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_540_);
v___x_542_ = v___x_533_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_545_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_snd_495_);
v___x_545_ = v___x_537_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_snd_495_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_545_);
v___x_547_ = v___x_533_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_a_531_);
lean_dec_ref(v_snd_495_);
v___x_551_ = lean_box(0);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_551_);
v___x_553_ = v___x_533_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_snd_495_);
v_a_556_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_530_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_530_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
}
}
v___jp_510_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_box(0);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_fst_565_, lean_object* v_snd_566_, lean_object* v_prop_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(v_fst_565_, v_snd_566_, v_prop_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec(v_fst_565_);
return v_res_576_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_unsigned_to_nat(32u);
v___x_586_ = lean_mk_empty_array_with_capacity(v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5(void){
_start:
{
size_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_588_ = ((size_t)5ULL);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_unsigned_to_nat(32u);
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4);
v___x_593_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_ctor_set(v___x_593_, 2, v___x_589_);
lean_ctor_set(v___x_593_, 3, v___x_589_);
lean_ctor_set_usize(v___x_593_, 4, v___x_588_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5);
v___x_595_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2);
v___x_596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_ctor_set(v___x_596_, 2, v___x_595_);
lean_ctor_set(v___x_596_, 3, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6);
v___x_598_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(lean_object* v_goal_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt;
v___x_609_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_608_, v___y_606_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_606_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v_maxSteps_613_; lean_object* v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v_maxSteps_613_ = lean_ctor_get(v___y_601_, 1);
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = 0;
v___x_616_ = 1;
v___x_617_ = 0;
v___x_618_ = lean_box(0);
lean_inc(v_maxSteps_613_);
v___x_619_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_619_, 0, v_maxSteps_613_);
lean_ctor_set(v___x_619_, 1, v___x_614_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 1, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 2, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 3, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 4, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 5, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 6, v___x_617_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 7, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 8, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 9, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 10, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 11, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 12, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 13, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 14, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 15, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 16, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 17, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 18, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 19, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 20, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 21, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 22, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 23, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 24, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 25, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 26, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 27, v___x_615_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 28, v___x_616_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_mk_empty_array_with_capacity(v___x_620_);
v___x_622_ = lean_array_push(v___x_621_, v_a_610_);
v___x_623_ = l_Lean_Options_empty;
v___x_624_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_619_, v___x_622_, v_a_612_, v___x_623_, v___y_603_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
lean_inc(v_goal_600_);
v___x_626_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_600_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___y_629_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
if (lean_obj_tag(v_a_627_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_682_; 
v_val_672_ = lean_ctor_get(v_a_627_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_a_627_);
if (v_isSharedCheck_682_ == 0)
{
v___x_674_ = v_a_627_;
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_val_672_);
lean_dec(v_a_627_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_682_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_fst_676_; lean_object* v_snd_677_; lean_object* v___f_678_; lean_object* v___x_680_; 
v_fst_676_ = lean_ctor_get(v_val_672_, 0);
lean_inc(v_fst_676_);
v_snd_677_ = lean_ctor_get(v_val_672_, 1);
lean_inc(v_snd_677_);
lean_dec(v_val_672_);
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed), 11, 2);
lean_closure_set(v___f_678_, 0, v_fst_676_);
lean_closure_set(v___f_678_, 1, v_snd_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___f_678_);
v___x_680_ = v___x_674_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___f_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
v___y_629_ = v___x_680_;
goto v___jp_628_;
}
}
}
else
{
lean_dec(v_a_627_);
v___y_629_ = v___x_618_;
goto v___jp_628_;
}
v___jp_628_:
{
lean_object* v___x_630_; 
lean_inc(v_goal_600_);
v___x_630_ = l_Lean_MVarId_getNondepPropHyps(v_goal_600_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__0));
v___x_633_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7);
v___x_634_ = l_Lean_Meta_simpGoal(v_goal_600_, v_a_625_, v___x_632_, v___y_629_, v___x_616_, v_a_631_, v___x_633_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_655_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_655_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_655_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_655_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_fst_639_; 
v_fst_639_ = lean_ctor_get(v_a_635_, 0);
lean_inc(v_fst_639_);
lean_dec(v_a_635_);
if (lean_obj_tag(v_fst_639_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_651_; 
v_val_640_ = lean_ctor_get(v_fst_639_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_fst_639_);
if (v_isSharedCheck_651_ == 0)
{
v___x_642_ = v_fst_639_;
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_val_640_);
lean_dec(v_fst_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_snd_644_; lean_object* v___x_646_; 
v_snd_644_ = lean_ctor_get(v_val_640_, 1);
lean_inc(v_snd_644_);
lean_dec(v_val_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_snd_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_snd_644_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_646_);
v___x_648_ = v___x_637_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_fst_639_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_618_);
v___x_653_ = v___x_637_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_618_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_634_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_634_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v___y_629_);
lean_dec(v_a_625_);
lean_dec(v_goal_600_);
v_a_664_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_630_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_630_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_625_);
lean_dec(v_goal_600_);
v_a_683_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_626_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_626_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_goal_600_);
v_a_691_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_624_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_624_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_610_);
lean_dec(v_goal_600_);
v_a_699_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_611_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_611_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_goal_600_);
v_a_707_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_609_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_609_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed(lean_object* v_goal_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(v_goal_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_723_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
