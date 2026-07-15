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
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Expr_hasMVar(v_e_113_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_e_113_);
return v___x_117_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_138_, v___y_139_);
lean_dec(v___y_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object* v_e_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_142_, v___y_144_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object* v_e_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_163_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object* v_mvarId_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object* v_00_u03b1_188_, lean_object* v_mvarId_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object* v_00_u03b1_197_, lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_197_, v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = l_Lean_Level_ofNat(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_box(0);
v___x_226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10);
v___x_229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
v___x_230_ = l_Lean_mkConst(v___x_229_, v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_239_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec_ref(v_b_239_);
v_a_247_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
lean_inc(v_a_247_);
v___x_248_ = l_Lean_FVarId_getType___redArg(v_a_247_, v___y_240_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_249_, v___y_241_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_251_, v___y_241_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_255_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_252_, 1);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v___x_261_ = l_Lean_Expr_cleanupAnnotations(v_a_253_);
v___x_262_ = l_Lean_Expr_isApp(v___x_261_);
if (v___x_262_ == 0)
{
lean_dec_ref(v___x_261_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_arg_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc_ref(v_arg_263_);
v___x_264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_261_);
v___x_265_ = l_Lean_Expr_isApp(v___x_264_);
if (v___x_265_ == 0)
{
lean_dec_ref(v___x_264_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_arg_266_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_arg_266_);
v___x_267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_264_);
v___x_268_ = l_Lean_Expr_isApp(v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_267_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_arg_269_ = lean_ctor_get(v___x_267_, 1);
lean_inc_ref(v_arg_269_);
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_267_);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_272_ = l_Lean_Expr_isConstOf(v___x_270_, v___x_271_);
lean_dec_ref(v___x_270_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_274_ = l_Lean_Expr_isConstOf(v_arg_266_, v___x_273_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_Expr_isConstOf(v_arg_263_, v___x_273_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_getNatValue_x3f(v_arg_266_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_302_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_302_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_302_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_302_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_297_; 
v_val_281_ = lean_ctor_get(v_a_277_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_277_);
if (v_isSharedCheck_297_ == 0)
{
v___x_283_ = v_a_277_;
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v_a_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
lean_inc(v_a_247_);
v___x_286_ = l_Lean_mkFVar(v_a_247_);
v___x_287_ = l_Lean_mkApp4(v___x_285_, v_arg_269_, v_arg_266_, v_arg_263_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_val_281_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_288_);
v___x_290_ = v___x_283_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_296_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_259_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_292_);
v___x_294_ = v___x_279_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec(v_a_277_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13));
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_298_);
v___x_300_ = v___x_279_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_303_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_276_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_276_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v___x_311_; 
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
v___x_311_ = l_Lean_Meta_getNatValue_x3f(v_arg_263_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec_ref(v_arg_263_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_335_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_335_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_335_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
if (lean_obj_tag(v_a_312_) == 1)
{
lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_330_; 
v_val_316_ = lean_ctor_get(v_a_312_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_312_);
if (v_isSharedCheck_330_ == 0)
{
v___x_318_ = v_a_312_;
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_dec(v_a_312_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_a_247_);
v___x_320_ = l_Lean_mkFVar(v_a_247_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_val_316_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_329_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_259_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_325_);
v___x_327_ = v___x_314_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v_a_312_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13));
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_331_);
v___x_333_ = v___x_314_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_311_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_311_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
}
v___jp_254_:
{
size_t v___x_256_; size_t v___x_257_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_238_, v___x_256_);
lean_inc_ref(v_a_255_);
v_i_238_ = v___x_257_;
v_b_239_ = v_a_255_;
goto _start;
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_252_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_252_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_250_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_250_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_248_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_248_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object* v_as_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_378_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_368_, v_sz_boxed_377_, v_i_boxed_378_, v_b_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_as_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_getPropHyps(v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v_sz_389_ = lean_array_size(v_a_386_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_386_, v_sz_389_, v___x_390_, v___x_388_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; 
v_fst_396_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_396_);
lean_dec(v_a_392_);
if (lean_obj_tag(v_fst_396_) == 0)
{
lean_object* v___x_398_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_387_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_387_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_fst_396_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_fst_396_, 1);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_391_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_391_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_385_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_385_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(lean_object* v_goal_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0));
v___x_435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_428_, v___f_434_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object* v_goal_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(lean_object* v_e_443_, lean_object* v___y_444_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_Expr_hasMVar(v_e_443_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_e_443_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v_mctx_449_; lean_object* v___x_450_; lean_object* v_fst_451_; lean_object* v_snd_452_; lean_object* v___x_453_; lean_object* v_cache_454_; lean_object* v_zetaDeltaFVarIds_455_; lean_object* v_postponed_456_; lean_object* v_diag_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_466_; 
v___x_448_ = lean_st_ref_get(v___y_444_);
v_mctx_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_mctx_449_);
lean_dec(v___x_448_);
v___x_450_ = l_Lean_instantiateMVarsCore(v_mctx_449_, v_e_443_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_fst_451_);
v_snd_452_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_snd_452_);
lean_dec_ref(v___x_450_);
v___x_453_ = lean_st_ref_take(v___y_444_);
v_cache_454_ = lean_ctor_get(v___x_453_, 1);
v_zetaDeltaFVarIds_455_ = lean_ctor_get(v___x_453_, 2);
v_postponed_456_ = lean_ctor_get(v___x_453_, 3);
v_diag_457_ = lean_ctor_get(v___x_453_, 4);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___x_453_, 0);
lean_dec(v_unused_467_);
v___x_459_ = v___x_453_;
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_diag_457_);
lean_inc(v_postponed_456_);
lean_inc(v_zetaDeltaFVarIds_455_);
lean_inc(v_cache_454_);
lean_dec(v___x_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v_snd_452_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_snd_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_cache_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_zetaDeltaFVarIds_455_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_postponed_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_diag_457_);
v___x_462_ = v_reuseFailAlloc_465_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_st_ref_set(v___y_444_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_fst_451_);
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg___boxed(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_e_468_, v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0(lean_object* v_e_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_e_472_, v___y_477_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___boxed(lean_object* v_e_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0(v_e_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(lean_object* v_fst_492_, lean_object* v_snd_493_, lean_object* v_prop_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_562_; 
v___x_503_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_spec__0___redArg(v_prop_494_, v___y_499_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_562_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_562_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_562_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = l_Lean_Expr_cleanupAnnotations(v_a_504_);
v___x_514_ = l_Lean_Expr_isApp(v___x_513_);
if (v___x_514_ == 0)
{
lean_dec_ref(v___x_513_);
lean_dec_ref(v_snd_493_);
goto v___jp_508_;
}
else
{
lean_object* v_arg_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_arg_515_ = lean_ctor_get(v___x_513_, 1);
lean_inc_ref(v_arg_515_);
v___x_516_ = l_Lean_Expr_appFnCleanup___redArg(v___x_513_);
v___x_517_ = l_Lean_Expr_isApp(v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v___x_516_);
lean_dec_ref(v_arg_515_);
lean_dec_ref(v_snd_493_);
goto v___jp_508_;
}
else
{
lean_object* v_arg_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_arg_518_ = lean_ctor_get(v___x_516_, 1);
lean_inc_ref(v_arg_518_);
v___x_519_ = l_Lean_Expr_appFnCleanup___redArg(v___x_516_);
v___x_520_ = l_Lean_Expr_isApp(v___x_519_);
if (v___x_520_ == 0)
{
lean_dec_ref(v___x_519_);
lean_dec_ref(v_arg_518_);
lean_dec_ref(v_arg_515_);
lean_dec_ref(v_snd_493_);
goto v___jp_508_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = l_Lean_Expr_appFnCleanup___redArg(v___x_519_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_523_ = l_Lean_Expr_isConstOf(v___x_521_, v___x_522_);
lean_dec_ref(v___x_521_);
if (v___x_523_ == 0)
{
lean_dec_ref(v_arg_518_);
lean_dec_ref(v_arg_515_);
lean_dec_ref(v_snd_493_);
goto v___jp_508_;
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; 
lean_del_object(v___x_506_);
v___x_524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_525_ = l_Lean_Expr_isConstOf(v_arg_518_, v___x_524_);
lean_dec_ref(v_arg_518_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v_arg_515_);
lean_dec_ref(v_snd_493_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Meta_getNatValue_x3f(v_arg_515_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec_ref(v_arg_515_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_553_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_553_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
if (lean_obj_tag(v_a_529_) == 1)
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_548_; 
v_val_533_ = lean_ctor_get(v_a_529_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_548_ == 0)
{
v___x_535_ = v_a_529_;
v_isShared_536_ = v_isSharedCheck_548_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v_a_529_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_548_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_eq(v_fst_492_, v_val_533_);
lean_dec(v_val_533_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_del_object(v___x_535_);
lean_dec_ref(v_snd_493_);
v___x_538_ = lean_box(0);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_538_);
v___x_540_ = v___x_531_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
else
{
lean_object* v___x_543_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_snd_493_);
v___x_543_ = v___x_535_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_snd_493_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_543_);
v___x_545_ = v___x_531_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_a_529_);
lean_dec_ref(v_snd_493_);
v___x_549_ = lean_box(0);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_549_);
v___x_551_ = v___x_531_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_snd_493_);
v_a_554_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_528_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_528_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
}
}
v___jp_508_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_fst_563_, lean_object* v_snd_564_, lean_object* v_prop_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(v_fst_563_, v_snd_564_, v_prop_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec(v_fst_563_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__1);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_unsigned_to_nat(32u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5(void){
_start:
{
size_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_586_ = ((size_t)5ULL);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__4);
v___x_591_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
lean_ctor_set(v___x_591_, 2, v___x_587_);
lean_ctor_set(v___x_591_, 3, v___x_587_);
lean_ctor_set_usize(v___x_591_, 4, v___x_586_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__5);
v___x_593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__2);
v___x_594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
lean_ctor_set(v___x_594_, 3, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__6);
v___x_596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__3);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(lean_object* v_goal_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecExt;
v___x_607_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_606_, v___y_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v_maxSteps_611_; lean_object* v___x_612_; uint8_t v___x_613_; uint8_t v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v_maxSteps_611_ = lean_ctor_get(v___y_599_, 1);
v___x_612_ = lean_unsigned_to_nat(2u);
v___x_613_ = 0;
v___x_614_ = 1;
v___x_615_ = 0;
v___x_616_ = lean_box(0);
lean_inc(v_maxSteps_611_);
v___x_617_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_617_, 0, v_maxSteps_611_);
lean_ctor_set(v___x_617_, 1, v___x_612_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 1, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 2, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 3, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 4, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 5, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 6, v___x_615_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 7, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 8, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 9, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 10, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 11, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 12, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 13, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 14, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 15, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 16, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 17, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 18, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 19, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 20, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 21, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 22, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 23, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 24, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 25, v___x_614_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 26, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 27, v___x_613_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3 + 28, v___x_614_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_mk_empty_array_with_capacity(v___x_618_);
v___x_620_ = lean_array_push(v___x_619_, v_a_608_);
v___x_621_ = l_Lean_Options_empty;
v___x_622_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_617_, v___x_620_, v_a_610_, v___x_621_, v___y_601_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
lean_inc(v_goal_598_);
v___x_624_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_598_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___y_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
if (lean_obj_tag(v_a_625_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_680_; 
v_val_670_ = lean_ctor_get(v_a_625_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_a_625_);
if (v_isSharedCheck_680_ == 0)
{
v___x_672_ = v_a_625_;
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v_a_625_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_680_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___f_676_; lean_object* v___x_678_; 
v_fst_674_ = lean_ctor_get(v_val_670_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v_val_670_, 1);
lean_inc(v_snd_675_);
lean_dec(v_val_670_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed), 11, 2);
lean_closure_set(v___f_676_, 0, v_fst_674_);
lean_closure_set(v___f_676_, 1, v_snd_675_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___f_676_);
v___x_678_ = v___x_672_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___f_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v___y_627_ = v___x_678_;
goto v___jp_626_;
}
}
}
else
{
lean_dec(v_a_625_);
v___y_627_ = v___x_616_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; 
lean_inc(v_goal_598_);
v___x_628_ = l_Lean_MVarId_getNondepPropHyps(v_goal_598_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__0));
v___x_631_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___closed__7);
v___x_632_ = l_Lean_Meta_simpGoal(v_goal_598_, v_a_623_, v___x_630_, v___y_627_, v___x_614_, v_a_629_, v___x_631_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_653_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_653_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_653_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_653_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; 
v_fst_637_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_fst_637_);
lean_dec(v_a_633_);
if (lean_obj_tag(v_fst_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_649_; 
v_val_638_ = lean_ctor_get(v_fst_637_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_649_ == 0)
{
v___x_640_ = v_fst_637_;
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_val_638_);
lean_dec(v_fst_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_snd_642_; lean_object* v___x_644_; 
v_snd_642_ = lean_ctor_get(v_val_638_, 1);
lean_inc(v_snd_642_);
lean_dec(v_val_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_snd_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_snd_642_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_644_);
v___x_646_ = v___x_635_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_651_; 
lean_dec(v_fst_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_616_);
v___x_651_ = v___x_635_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_616_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_a_654_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_632_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_632_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v___y_627_);
lean_dec(v_a_623_);
lean_dec(v_goal_598_);
v_a_662_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_628_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_628_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec(v_a_623_);
lean_dec(v_goal_598_);
v_a_681_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_624_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_624_);
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
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_goal_598_);
v_a_689_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_622_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_622_);
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
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_a_608_);
lean_dec(v_goal_598_);
v_a_697_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_609_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_609_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_goal_598_);
v_a_705_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_607_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_607_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1___boxed(lean_object* v_goal_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__1(v_goal_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_721_;
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
