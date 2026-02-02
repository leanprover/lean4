// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadVars
// Imports: public import Lean.Compiler.IR.FreeVars
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
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elim_dead"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 89, 123, 66, 198, 100, 59, 24)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 1, 131, 81, 163, 33, 163, 70)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ElimDeadVars"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 46, 21, 57, 89, 188, 185, 2)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 145, 217, 145, 157, 129, 249, 99)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 22, 149, 9, 61, 40, 9, 82)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 27, 93, 115, 16, 36, 109, 217)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 166, 140, 187, 2, 168, 210, 34)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 68, 200, 171, 180, 146, 130, 44)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 51, 195, 48, 22, 178, 130, 58)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 31, 165, 151, 22, 206, 37, 244)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 75, 126, 26, 240, 138, 23, 140)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 144, 25, 32, 165, 179, 67, 224)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)(((size_t)(172251937) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(47, 92, 242, 69, 81, 128, 114, 248)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 36, 112, 251, 226, 190, 96, 248)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__29_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 58, 8, 58, 231, 204, 27, 17)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__29_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__29_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__30_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__29_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(225, 151, 23, 129, 220, 79, 126, 177)}};
static const lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__30_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__30_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Array_isEmpty___redArg(x_2);
return x_3;
}
case 8:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
default: 
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_nat_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_instInhabitedFnBody_default__1;
x_6 = l_Array_back_x21___redArg(x_5, x_1);
x_7 = lean_array_pop(x_1);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_13);
x_14 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(x_12, x_3);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_safeToElim(x_13);
lean_dec_ref(x_13);
if (x_15 == 0)
{
goto block_11;
}
else
{
if (x_14 == 0)
{
lean_dec_ref(x_6);
x_1 = x_7;
goto _start;
}
else
{
goto block_11;
}
}
}
else
{
lean_dec_ref(x_13);
goto block_11;
}
}
case 1:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(x_17, x_3);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_6);
x_1 = x_7;
goto _start;
}
else
{
goto block_11;
}
}
default: 
{
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
x_8 = l_Lean_IR_FnBody_collectFreeIndices(x_6, x_3);
x_9 = l_Lean_IR_FnBody_setBody(x_6, x_2);
x_1 = x_7;
x_2 = x_9;
x_3 = x_8;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_freeIndices(x_2);
x_4 = l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_reshapeWithoutDead_reshape(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = l_Lean_IR_FnBody_elimDead(x_15);
lean_ctor_set(x_5, 2, x_16);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_21 = l_Lean_IR_FnBody_elimDead(x_19);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_20);
x_8 = x_22;
goto block_13;
}
}
else
{
x_8 = x_5;
goto block_13;
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = l_Lean_IR_FnBody_elimDead(x_15);
lean_ctor_set(x_5, 1, x_16);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = l_Lean_IR_FnBody_elimDead(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_8 = x_20;
goto block_13;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = l_Lean_IR_FnBody_elimDead(x_22);
lean_ctor_set(x_5, 0, x_23);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_IR_FnBody_elimDead(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_8 = x_26;
goto block_13;
}
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0(x_5, x_6, x_3);
if (lean_obj_tag(x_4) == 9)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_array_size(x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1(x_10, x_6, x_9);
lean_ctor_set(x_4, 3, x_11);
x_12 = l_Lean_IR_reshapeWithoutDead(x_7, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_17 = lean_array_size(x_16);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1(x_17, x_6, x_16);
x_19 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean_IR_reshapeWithoutDead(x_7, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_IR_reshapeWithoutDead(x_7, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_FnBody_elimDead_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_elimDead(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_elimDead(x_2);
x_4 = l_Lean_IR_Decl_updateBody_x21(x_1, x_3);
return x_4;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_));
x_3 = 1;
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn___closed__30_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_FreeVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___private_Lean_Compiler_IR_ElimDeadVars_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_ElimDeadVars_172251937____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
