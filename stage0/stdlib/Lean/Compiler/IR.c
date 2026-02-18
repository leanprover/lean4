// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: public import Lean.Compiler.IR.AddExtern public import Lean.Compiler.IR.Basic public import Lean.Compiler.IR.Format public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.PushProj public import Lean.Compiler.IR.NormIds public import Lean.Compiler.IR.Checker public import Lean.Compiler.IR.RC public import Lean.Compiler.IR.ExpandResetReuse public import Lean.Compiler.IR.UnboxResult public import Lean.Compiler.IR.EmitC public import Lean.Compiler.IR.Sorry public import Lean.Compiler.IR.ToIR public import Lean.Compiler.IR.ToIRType public import Lean.Compiler.IR.Meta public import Lean.Compiler.IR.Toposort public import Lean.Compiler.IR.SimpleGroundExpr public import Lean.Compiler.IR.ElimDeadVars public import Lean.Compiler.IR.LLVMBindings public import Lean.Compiler.IR.EmitLLVM
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_IR_compile_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_IR_compile_spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_Decl_detectSimpleGround(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_compile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "push_proj"};
static const lean_object* l_Lean_IR_compile___closed__0 = (const lean_object*)&l_Lean_IR_compile___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_IR_compile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 5, 19, 211, 37, 77, 187, 11)}};
static const lean_object* l_Lean_IR_compile___closed__1 = (const lean_object*)&l_Lean_IR_compile___closed__1_value;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__2;
static const lean_string_object l_Lean_IR_compile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_IR_compile___closed__3 = (const lean_object*)&l_Lean_IR_compile___closed__3_value;
static const lean_ctor_object l_Lean_IR_compile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 131, 177, 30, 113, 24, 63, 83)}};
static const lean_object* l_Lean_IR_compile___closed__4 = (const lean_object*)&l_Lean_IR_compile___closed__4_value;
static lean_object* l_Lean_IR_compile___closed__5;
static const lean_string_object l_Lean_IR_compile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lean_IR_compile___closed__6 = (const lean_object*)&l_Lean_IR_compile___closed__6_value;
static const lean_ctor_object l_Lean_IR_compile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__6_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 38, 228, 229, 249, 19, 211)}};
static const lean_object* l_Lean_IR_compile___closed__7 = (const lean_object*)&l_Lean_IR_compile___closed__7_value;
static lean_object* l_Lean_IR_compile___closed__8;
static const lean_string_object l_Lean_IR_compile___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "rc"};
static const lean_object* l_Lean_IR_compile___closed__9 = (const lean_object*)&l_Lean_IR_compile___closed__9_value;
static const lean_ctor_object l_Lean_IR_compile___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__9_value),LEAN_SCALAR_PTR_LITERAL(47, 196, 226, 82, 255, 49, 236, 119)}};
static const lean_object* l_Lean_IR_compile___closed__10 = (const lean_object*)&l_Lean_IR_compile___closed__10_value;
static lean_object* l_Lean_IR_compile___closed__11;
static const lean_string_object l_Lean_IR_compile___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expand_reset_reuse"};
static const lean_object* l_Lean_IR_compile___closed__12 = (const lean_object*)&l_Lean_IR_compile___closed__12_value;
static const lean_ctor_object l_Lean_IR_compile___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__12_value),LEAN_SCALAR_PTR_LITERAL(60, 21, 194, 70, 67, 90, 93, 241)}};
static const lean_object* l_Lean_IR_compile___closed__13 = (const lean_object*)&l_Lean_IR_compile___closed__13_value;
static lean_object* l_Lean_IR_compile___closed__14;
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_inferMeta(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_toposortDecls(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_compiler_reuse;
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 1, 131, 81, 163, 33, 163, 70)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(162, 139, 175, 27, 40, 192, 102, 32)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 96, 47, 177, 82, 29, 15, 157)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 7, 65, 12, 54, 59, 188, 77)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 84, 185, 229, 139, 51, 62, 203)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 144, 178, 118, 149, 122, 14, 223)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 197, 105, 177, 43, 178, 129, 150)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 29, 106, 3, 202, 7, 21, 93)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 7, 171, 237, 105, 253, 200)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)(((size_t)(640659120) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(229, 36, 140, 195, 28, 197, 35, 162)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 214, 120, 45, 15, 18, 157, 168)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 216, 254, 226, 44, 82, 146, 22)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(51, 184, 72, 13, 133, 251, 4, 217)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_compile___closed__6_value),LEAN_SCALAR_PTR_LITERAL(68, 154, 177, 167, 20, 181, 135, 8)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_compile___closed__3_value),LEAN_SCALAR_PTR_LITERAL(88, 165, 93, 202, 154, 177, 169, 12)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_IR_compile_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_IR_compile_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_IR_compile_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_IR_Decl_detectSimpleGround(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_expandResetReuse(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_pushProj(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_IR_compile___closed__1));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_IR_compile___closed__4));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_IR_compile___closed__7));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_IR_compile___closed__10));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_IR_compile___closed__13));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = ((lean_object*)(l_Lean_IR_compile___closed__7));
x_67 = l_Lean_IR_compile___closed__8;
lean_inc_ref(x_1);
x_68 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_67, x_66, x_1, x_2, x_3);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_dec_ref(x_68);
lean_inc_ref(x_1);
x_69 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_dec_ref(x_69);
x_70 = l_Lean_IR_explicitRC___redArg(x_1, x_3);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = ((lean_object*)(l_Lean_IR_compile___closed__10));
x_73 = l_Lean_IR_compile___closed__11;
lean_inc(x_71);
x_74 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_73, x_72, x_71, x_2, x_3);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec_ref(x_74);
x_75 = lean_ctor_get(x_2, 2);
x_76 = l_Lean_Compiler_LCNF_compiler_reuse;
x_77 = l_Lean_Option_get___at___00Lean_IR_compile_spec__2(x_75, x_76);
if (x_77 == 0)
{
x_29 = x_71;
x_30 = x_2;
x_31 = x_3;
x_32 = lean_box(0);
goto block_65;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_array_size(x_71);
x_79 = 0;
x_80 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(x_78, x_79, x_71);
x_81 = ((lean_object*)(l_Lean_IR_compile___closed__13));
x_82 = l_Lean_IR_compile___closed__14;
lean_inc_ref(x_80);
x_83 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_82, x_81, x_80, x_2, x_3);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_29 = x_80;
x_30 = x_2;
x_31 = x_3;
x_32 = lean_box(0);
goto block_65;
}
else
{
uint8_t x_84; 
lean_dec_ref(x_80);
lean_dec(x_3);
lean_dec_ref(x_2);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_71);
lean_dec(x_3);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_74);
if (x_87 == 0)
{
return x_74;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
lean_dec(x_74);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_70;
}
}
else
{
uint8_t x_90; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_69);
if (x_90 == 0)
{
return x_69;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_69, 0);
lean_inc(x_91);
lean_dec(x_69);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_68);
if (x_93 == 0)
{
return x_68;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_68, 0);
lean_inc(x_94);
lean_dec(x_68);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
block_20:
{
lean_object* x_9; 
x_9 = l_Lean_IR_addDecls(x_6, x_5, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
x_10 = l_Lean_IR_inferMeta(x_6, x_5, x_7);
lean_dec(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec_ref(x_6);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
block_28:
{
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_5 = x_21;
x_6 = x_22;
x_7 = x_23;
x_8 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_25; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
block_65:
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_array_size(x_29);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(x_33, x_34, x_29);
x_36 = ((lean_object*)(l_Lean_IR_compile___closed__1));
x_37 = l_Lean_IR_compile___closed__2;
lean_inc_ref(x_35);
x_38 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_37, x_36, x_35, x_30, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l_Lean_IR_updateSorryDep(x_35, x_30, x_31);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = ((lean_object*)(l_Lean_IR_compile___closed__4));
x_42 = l_Lean_IR_compile___closed__5;
lean_inc(x_40);
x_43 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_42, x_41, x_40, x_30, x_31);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec_ref(x_43);
lean_inc(x_40);
x_44 = l_Lean_IR_checkDecls(x_40, x_30, x_31);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
lean_inc(x_31);
lean_inc_ref(x_30);
x_45 = l_Lean_IR_toposortDecls(x_40, x_30, x_31);
lean_dec(x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_46);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
x_5 = x_30;
x_6 = x_46;
x_7 = x_31;
x_8 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_49 == 0)
{
x_5 = x_30;
x_6 = x_46;
x_7 = x_31;
x_8 = lean_box(0);
goto block_20;
}
else
{
size_t x_52; lean_object* x_53; 
x_52 = lean_usize_of_nat(x_48);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_46, x_34, x_52, x_50, x_30, x_31);
x_21 = x_30;
x_22 = x_46;
x_23 = x_31;
x_24 = x_53;
goto block_28;
}
}
else
{
size_t x_54; lean_object* x_55; 
x_54 = lean_usize_of_nat(x_48);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_46, x_34, x_54, x_50, x_30, x_31);
x_21 = x_30;
x_22 = x_46;
x_23 = x_31;
x_24 = x_55;
goto block_28;
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
return x_45;
}
}
else
{
uint8_t x_56; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
lean_dec(x_44);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_31);
lean_dec_ref(x_30);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
return x_43;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
return x_39;
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_35);
lean_dec(x_31);
lean_dec_ref(x_30);
x_62 = !lean_is_exclusive(x_38);
if (x_62 == 0)
{
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_compile(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
x_7 = 1;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_8);
x_9 = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
x_10 = l_Lean_registerTraceClass(x_9, x_7, x_4);
return x_10;
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_PushProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Meta(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Toposort(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_SimpleGroundExpr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_RC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpleGroundExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitLLVM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_compile___closed__2 = _init_l_Lean_IR_compile___closed__2();
lean_mark_persistent(l_Lean_IR_compile___closed__2);
l_Lean_IR_compile___closed__5 = _init_l_Lean_IR_compile___closed__5();
lean_mark_persistent(l_Lean_IR_compile___closed__5);
l_Lean_IR_compile___closed__8 = _init_l_Lean_IR_compile___closed__8();
lean_mark_persistent(l_Lean_IR_compile___closed__8);
l_Lean_IR_compile___closed__11 = _init_l_Lean_IR_compile___closed__11();
lean_mark_persistent(l_Lean_IR_compile___closed__11);
l_Lean_IR_compile___closed__14 = _init_l_Lean_IR_compile___closed__14();
lean_mark_persistent(l_Lean_IR_compile___closed__14);
if (builtin) {res = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
