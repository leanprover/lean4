// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: public import Lean.Compiler.IR.AddExtern public import Lean.Compiler.IR.Basic public import Lean.Compiler.IR.Format public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.NormIds public import Lean.Compiler.IR.Checker public import Lean.Compiler.IR.UnboxResult public import Lean.Compiler.IR.Sorry public import Lean.Compiler.IR.ToIR public import Lean.Compiler.IR.ToIRType public import Lean.Compiler.IR.Meta public import Lean.Compiler.IR.LLVMBindings public import Lean.Compiler.IR.EmitLLVM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_inferMeta(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_IR_compile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lean_IR_compile___closed__0 = (const lean_object*)&l_Lean_IR_compile___closed__0_value;
static const lean_ctor_object l_Lean_IR_compile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 5, 38, 228, 229, 249, 19, 211)}};
static const lean_object* l_Lean_IR_compile___closed__1 = (const lean_object*)&l_Lean_IR_compile___closed__1_value;
static lean_once_cell_t l_Lean_IR_compile___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_compile___closed__2;
static const lean_string_object l_Lean_IR_compile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_IR_compile___closed__3 = (const lean_object*)&l_Lean_IR_compile___closed__3_value;
static const lean_ctor_object l_Lean_IR_compile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_compile___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 131, 177, 30, 113, 24, 63, 83)}};
static const lean_object* l_Lean_IR_compile___closed__4 = (const lean_object*)&l_Lean_IR_compile___closed__4_value;
static lean_once_cell_t l_Lean_IR_compile___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_compile___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
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
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_compile___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 154, 177, 167, 20, 181, 135, 8)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_compile___closed__3_value),LEAN_SCALAR_PTR_LITERAL(88, 165, 93, 202, 154, 177, 169, 12)}};
static const lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_IR_compile___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = ((lean_object*)(l_Lean_IR_compile___closed__1));
v___x_5_ = l_Lean_IR_tracePrefixOptionName;
v___x_6_ = l_Lean_Name_append(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__5(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = ((lean_object*)(l_Lean_IR_compile___closed__4));
v___x_11_ = l_Lean_IR_tracePrefixOptionName;
v___x_12_ = l_Lean_Name_append(v___x_11_, v___x_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object* v_decls_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = ((lean_object*)(l_Lean_IR_compile___closed__1));
v___x_18_ = lean_obj_once(&l_Lean_IR_compile___closed__2, &l_Lean_IR_compile___closed__2_once, _init_l_Lean_IR_compile___closed__2);
lean_inc_ref(v_decls_13_);
v___x_19_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_18_, v___x_17_, v_decls_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v___x_20_; 
lean_dec_ref(v___x_19_);
lean_inc_ref(v_decls_13_);
v___x_20_ = l_Lean_IR_checkDecls(v_decls_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v___x_21_; 
lean_dec_ref(v___x_20_);
v___x_21_ = l_Lean_IR_updateSorryDep(v_decls_13_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = ((lean_object*)(l_Lean_IR_compile___closed__4));
v___x_24_ = lean_obj_once(&l_Lean_IR_compile___closed__5, &l_Lean_IR_compile___closed__5_once, _init_l_Lean_IR_compile___closed__5);
lean_inc(v_a_22_);
v___x_25_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_24_, v___x_23_, v_a_22_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v___x_26_; 
lean_dec_ref(v___x_25_);
v___x_26_ = l_Lean_IR_addDecls(v_a_22_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v___x_27_; 
lean_dec_ref(v___x_26_);
v___x_27_ = l_Lean_IR_inferMeta(v_a_22_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_34_ == 0)
{
lean_object* v_unused_35_; 
v_unused_35_ = lean_ctor_get(v___x_27_, 0);
lean_dec(v_unused_35_);
v___x_29_ = v___x_27_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_dec(v___x_27_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v_a_22_);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_22_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v_a_22_);
v_a_36_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_27_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_27_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
lean_dec(v_a_22_);
v_a_44_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_26_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_26_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
else
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_a_22_);
v_a_52_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_25_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_25_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
else
{
return v___x_21_;
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref(v_decls_13_);
v_a_60_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_20_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_20_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
lean_dec_ref(v_decls_13_);
v_a_68_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v___x_19_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_19_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object* v_decls_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_IR_compile(v_decls_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
v___x_152_ = 0;
v___x_153_ = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
v___x_154_ = l_Lean_registerTraceClass(v___x_151_, v___x_152_, v___x_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; 
lean_dec_ref(v___x_154_);
v___x_155_ = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
v___x_156_ = 1;
v___x_157_ = l_Lean_registerTraceClass(v___x_155_, v___x_156_, v___x_153_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec_ref(v___x_157_);
v___x_158_ = ((lean_object*)(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_));
v___x_159_ = l_Lean_registerTraceClass(v___x_158_, v___x_156_, v___x_153_);
return v___x_159_;
}
else
{
return v___x_157_;
}
}
else
{
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
return v_res_161_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_Checker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_UnboxResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_EmitLLVM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Meta(uint8_t builtin);
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
res = initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(builtin);
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
res = initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitLLVM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR(builtin);
}
#ifdef __cplusplus
}
#endif
