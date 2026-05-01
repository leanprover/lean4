// Lean compiler output
// Module: Lean.Compiler.MetaAttr
// Imports: public import Lean.EnvExtension
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MetaAttr"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 82, 98, 20, 235, 174, 156, 157)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(26, 118, 206, 146, 141, 20, 36, 51)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 221, 14, 170, 191, 134, 253, 17)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "metaExt"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 2, 121, 18, 238, 241, 123, 158)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
LEAN_EXPORT lean_object* l_Lean_markMeta(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isMarkedMeta___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declMetaExt"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 84, 56, 43, 91, 46, 76, 198)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isDeclMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_isDeclMeta___closed__0 = (const lean_object*)&l_Lean_isDeclMeta___closed__0_value;
static const lean_string_object l_Lean_isDeclMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_isDeclMeta___closed__1 = (const lean_object*)&l_Lean_isDeclMeta___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getIRPhases_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getIRPhases_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_getIRPhases_spec__0___closed__6_value;
LEAN_EXPORT uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_getIRPhases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_getIRPhases___closed__0 = (const lean_object*)&l_Lean_getIRPhases___closed__0_value;
static const lean_string_object l_Lean_getIRPhases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_getIRPhases___closed__1 = (const lean_object*)&l_Lean_getIRPhases___closed__1_value;
static const lean_string_object l_Lean_getIRPhases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_getIRPhases___closed__2 = (const lean_object*)&l_Lean_getIRPhases___closed__2_value;
static lean_once_cell_t l_Lean_getIRPhases___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getIRPhases___closed__3;
LEAN_EXPORT uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_));
v___x_31_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_));
v___x_32_ = l_Lean_mkTagDeclarationExtension(v___x_30_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2____boxed(lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_markMeta(lean_object* v_env_35_, lean_object* v_declName_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v___x_38_ = l_Lean_TagDeclarationExtension_tag(v___x_37_, v_env_35_, v_declName_36_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Lean_isMarkedMeta(lean_object* v_env_39_, lean_object* v_declName_40_){
_start:
{
lean_object* v___x_41_; lean_object* v_toEnvExtension_42_; lean_object* v_asyncMode_43_; uint8_t v___x_44_; 
v___x_41_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v_toEnvExtension_42_ = lean_ctor_get(v___x_41_, 0);
v_asyncMode_43_ = lean_ctor_get(v_toEnvExtension_42_, 2);
v___x_44_ = l_Lean_TagDeclarationExtension_isTagged(v___x_41_, v_env_39_, v_declName_40_, v_asyncMode_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_isMarkedMeta___boxed(lean_object* v_env_45_, lean_object* v_declName_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lean_isMarkedMeta(v_env_45_, v_declName_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_NameSet_empty;
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x_51_);
lean_dec_ref(v_x_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_es_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_array_mk(v_es_53_);
return v___x_54_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_x1_55_, lean_object* v_x2_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_NameSet_contains(v_x1_55_, v_x2_56_);
if (v___x_57_ == 0)
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_x1_60_, lean_object* v_x2_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x1_60_, v_x2_61_);
lean_dec(v_x2_61_);
lean_dec(v_x1_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_hi_64_, lean_object* v_pivot_65_, lean_object* v_as_66_, lean_object* v_i_67_, lean_object* v_k_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_lt(v_k_68_, v_hi_64_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_k_68_);
v___x_70_ = lean_array_fswap(v_as_66_, v_i_67_, v_hi_64_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_i_67_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_array_fget_borrowed(v_as_66_, v_k_68_);
v___x_73_ = l_Lean_Name_quickLt(v___x_72_, v_pivot_65_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_k_68_, v___x_74_);
lean_dec(v_k_68_);
v_k_68_ = v___x_75_;
goto _start;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = lean_array_fswap(v_as_66_, v_i_67_, v_k_68_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_i_67_, v___x_78_);
lean_dec(v_i_67_);
v___x_80_ = lean_nat_add(v_k_68_, v___x_78_);
lean_dec(v_k_68_);
v_as_66_ = v___x_77_;
v_i_67_ = v___x_79_;
v_k_68_ = v___x_80_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object* v_hi_82_, lean_object* v_pivot_83_, lean_object* v_as_84_, lean_object* v_i_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_82_, v_pivot_83_, v_as_84_, v_i_85_, v_k_86_);
lean_dec(v_pivot_83_);
lean_dec(v_hi_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_88_, lean_object* v_as_89_, lean_object* v_lo_90_, lean_object* v_hi_91_){
_start:
{
lean_object* v___y_93_; uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_lt(v_lo_90_, v_hi_91_);
if (v___x_103_ == 0)
{
lean_dec(v_lo_90_);
return v_as_89_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_mid_106_; lean_object* v___y_108_; lean_object* v___y_114_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_104_ = lean_nat_add(v_lo_90_, v_hi_91_);
v___x_105_ = lean_unsigned_to_nat(1u);
v_mid_106_ = lean_nat_shiftr(v___x_104_, v___x_105_);
lean_dec(v___x_104_);
v___x_119_ = lean_array_fget_borrowed(v_as_89_, v_mid_106_);
v___x_120_ = lean_array_fget_borrowed(v_as_89_, v_lo_90_);
v___x_121_ = l_Lean_Name_quickLt(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
v___y_114_ = v_as_89_;
goto v___jp_113_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = lean_array_fswap(v_as_89_, v_lo_90_, v_mid_106_);
v___y_114_ = v___x_122_;
goto v___jp_113_;
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_array_fget_borrowed(v___y_108_, v_mid_106_);
v___x_110_ = lean_array_fget_borrowed(v___y_108_, v_hi_91_);
v___x_111_ = l_Lean_Name_quickLt(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec(v_mid_106_);
v___y_93_ = v___y_108_;
goto v___jp_92_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_array_fswap(v___y_108_, v_mid_106_, v_hi_91_);
lean_dec(v_mid_106_);
v___y_93_ = v___x_112_;
goto v___jp_92_;
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_array_fget_borrowed(v___y_114_, v_hi_91_);
v___x_116_ = lean_array_fget_borrowed(v___y_114_, v_lo_90_);
v___x_117_ = l_Lean_Name_quickLt(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
v___y_108_ = v___y_114_;
goto v___jp_107_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_array_fswap(v___y_114_, v_lo_90_, v_hi_91_);
v___y_108_ = v___x_118_;
goto v___jp_107_;
}
}
}
v___jp_92_:
{
lean_object* v_pivot_94_; lean_object* v___x_95_; lean_object* v_fst_96_; lean_object* v_snd_97_; uint8_t v___x_98_; 
v_pivot_94_ = lean_array_fget(v___y_93_, v_hi_91_);
lean_inc_n(v_lo_90_, 2);
v___x_95_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_91_, v_pivot_94_, v___y_93_, v_lo_90_, v_lo_90_);
lean_dec(v_pivot_94_);
v_fst_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_fst_96_);
v_snd_97_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_snd_97_);
lean_dec_ref(v___x_95_);
v___x_98_ = lean_nat_dec_le(v_hi_91_, v_fst_96_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_88_, v_snd_97_, v_lo_90_, v_fst_96_);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_fst_96_, v___x_100_);
lean_dec(v_fst_96_);
v_as_89_ = v___x_99_;
v_lo_90_ = v___x_101_;
goto _start;
}
else
{
lean_dec(v_fst_96_);
lean_dec(v_lo_90_);
return v_snd_97_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_123_, lean_object* v_as_124_, lean_object* v_lo_125_, lean_object* v_hi_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_123_, v_as_124_, v_lo_125_, v_hi_126_);
lean_dec(v_hi_126_);
lean_dec(v_n_123_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
return v_x_128_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; 
v_head_130_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_x_129_, 1);
lean_inc(v_tail_131_);
lean_dec_ref(v_x_129_);
v___x_132_ = lean_array_push(v_x_128_, v_head_130_);
v_x_128_ = v___x_132_;
v_x_129_ = v_tail_131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v___x_134_, lean_object* v_env_135_, lean_object* v_s_136_, lean_object* v_entries_137_){
_start:
{
lean_object* v___x_138_; lean_object* v_decls_139_; lean_object* v___x_140_; lean_object* v___y_142_; lean_object* v___y_143_; uint8_t v___x_146_; 
v___x_138_ = lean_mk_empty_array_with_capacity(v___x_134_);
lean_inc_ref(v___x_138_);
v_decls_139_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(v___x_138_, v_entries_137_);
v___x_140_ = lean_array_get_size(v_decls_139_);
v___x_146_ = lean_nat_dec_eq(v___x_140_, v___x_134_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___y_150_; uint8_t v___x_152_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_sub(v___x_140_, v___x_147_);
v___x_152_ = lean_nat_dec_le(v___x_134_, v___x_148_);
if (v___x_152_ == 0)
{
lean_dec(v___x_134_);
lean_inc(v___x_148_);
v___y_150_ = v___x_148_;
goto v___jp_149_;
}
else
{
v___y_150_ = v___x_134_;
goto v___jp_149_;
}
v___jp_149_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v___y_150_, v___x_148_);
if (v___x_151_ == 0)
{
lean_dec(v___x_148_);
lean_inc(v___y_150_);
v___y_142_ = v___y_150_;
v___y_143_ = v___y_150_;
goto v___jp_141_;
}
else
{
v___y_142_ = v___y_150_;
v___y_143_ = v___x_148_;
goto v___jp_141_;
}
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_134_);
lean_inc_ref(v___x_138_);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_138_);
lean_ctor_set(v___x_153_, 1, v___x_138_);
lean_ctor_set(v___x_153_, 2, v_decls_139_);
return v___x_153_;
}
v___jp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v___x_140_, v_decls_139_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_inc_ref(v___x_138_);
v___x_145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_138_);
lean_ctor_set(v___x_145_, 1, v___x_138_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v___x_154_, lean_object* v_env_155_, lean_object* v_s_156_, lean_object* v_entries_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v___x_154_, v_env_155_, v_s_156_, v_entries_157_);
lean_dec(v_s_156_);
lean_dec_ref(v_env_155_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_));
v___x_186_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(lean_object* v_n_189_, lean_object* v_as_190_, lean_object* v_lo_191_, lean_object* v_hi_192_, lean_object* v_w_193_, lean_object* v_hlo_194_, lean_object* v_hhi_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_189_, v_as_190_, v_lo_191_, v_hi_192_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_197_, lean_object* v_as_198_, lean_object* v_lo_199_, lean_object* v_hi_200_, lean_object* v_w_201_, lean_object* v_hlo_202_, lean_object* v_hhi_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(v_n_197_, v_as_198_, v_lo_199_, v_hi_200_, v_w_201_, v_hlo_202_, v_hhi_203_);
lean_dec(v_hi_200_);
lean_dec(v_n_197_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_n_205_, lean_object* v_lo_206_, lean_object* v_hi_207_, lean_object* v_hhi_208_, lean_object* v_pivot_209_, lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_k_212_, lean_object* v_ilo_213_, lean_object* v_ik_214_, lean_object* v_w_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_207_, v_pivot_209_, v_as_210_, v_i_211_, v_k_212_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_n_217_, lean_object* v_lo_218_, lean_object* v_hi_219_, lean_object* v_hhi_220_, lean_object* v_pivot_221_, lean_object* v_as_222_, lean_object* v_i_223_, lean_object* v_k_224_, lean_object* v_ilo_225_, lean_object* v_ik_226_, lean_object* v_w_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(v_n_217_, v_lo_218_, v_hi_219_, v_hhi_220_, v_pivot_221_, v_as_222_, v_i_223_, v_k_224_, v_ilo_225_, v_ik_226_, v_w_227_);
lean_dec(v_pivot_221_);
lean_dec(v_hi_219_);
lean_dec(v_lo_218_);
lean_dec(v_n_217_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(uint8_t v___x_229_, lean_object* v_as_230_, lean_object* v_k_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_m_236_; lean_object* v_a_237_; uint8_t v___x_238_; 
v___x_234_ = lean_nat_add(v_x_232_, v_x_233_);
v___x_235_ = lean_unsigned_to_nat(1u);
v_m_236_ = lean_nat_shiftr(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
v_a_237_ = lean_array_fget_borrowed(v_as_230_, v_m_236_);
v___x_238_ = l_Lean_Name_quickLt(v_a_237_, v_k_231_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
lean_dec(v_x_233_);
v___x_239_ = l_Lean_Name_quickLt(v_k_231_, v_a_237_);
if (v___x_239_ == 0)
{
lean_dec(v_m_236_);
lean_dec(v_x_232_);
return v___x_229_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v_m_236_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_nat_sub(v_m_236_, v___x_235_);
lean_dec(v_m_236_);
v___x_243_ = lean_nat_dec_lt(v___x_242_, v_x_232_);
if (v___x_243_ == 0)
{
v_x_233_ = v___x_242_;
goto _start;
}
else
{
lean_dec(v___x_242_);
lean_dec(v_x_232_);
return v___x_238_;
}
}
else
{
lean_dec(v_m_236_);
lean_dec(v_x_232_);
return v___x_238_;
}
}
}
else
{
lean_object* v___x_245_; uint8_t v___x_246_; 
lean_dec(v_x_232_);
v___x_245_ = lean_nat_add(v_m_236_, v___x_235_);
lean_dec(v_m_236_);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_x_233_);
if (v___x_246_ == 0)
{
lean_dec(v___x_245_);
lean_dec(v_x_233_);
return v___x_246_;
}
else
{
v_x_232_ = v___x_245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object* v___x_248_, lean_object* v_as_249_, lean_object* v_k_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v___x_435__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v___x_435__boxed_253_ = lean_unbox(v___x_248_);
v_res_254_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_435__boxed_253_, v_as_249_, v_k_250_, v_x_251_, v_x_252_);
lean_dec(v_k_250_);
lean_dec_ref(v_as_249_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object* v_env_260_, lean_object* v_declName_261_){
_start:
{
lean_object* v___x_262_; uint8_t v_isModule_263_; 
v___x_262_ = l_Lean_Environment_header(v_env_260_);
v_isModule_263_ = lean_ctor_get_uint8(v___x_262_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_262_);
if (v_isModule_263_ == 0)
{
uint8_t v___x_264_; 
lean_dec_ref(v_env_260_);
v___x_264_ = 1;
return v___x_264_;
}
else
{
uint8_t v___x_265_; lean_object* v___y_267_; 
v___x_265_ = 0;
if (lean_obj_tag(v_declName_261_) == 1)
{
lean_object* v_pre_288_; lean_object* v_str_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_pre_288_ = lean_ctor_get(v_declName_261_, 0);
v_str_289_ = lean_ctor_get(v_declName_261_, 1);
v___x_290_ = ((lean_object*)(l_Lean_isDeclMeta___closed__1));
v___x_291_ = lean_string_dec_eq(v_str_289_, v___x_290_);
if (v___x_291_ == 0)
{
v___y_267_ = v_declName_261_;
goto v___jp_266_;
}
else
{
v___y_267_ = v_pre_288_;
goto v___jp_266_;
}
}
else
{
v___y_267_ = v_declName_261_;
goto v___jp_266_;
}
v___jp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_260_, v_declName_261_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v_toEnvExtension_270_; lean_object* v_asyncMode_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_269_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_270_ = lean_ctor_get(v___x_269_, 0);
v_asyncMode_271_ = lean_ctor_get(v_toEnvExtension_270_, 2);
v___x_272_ = lean_box(1);
v___x_273_ = lean_box(0);
v___x_274_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_272_, v___x_269_, v_env_260_, v_asyncMode_271_, v___x_273_);
v___x_275_ = l_Lean_NameSet_contains(v___x_274_, v___y_267_);
lean_dec(v___x_274_);
return v___x_275_;
}
else
{
lean_object* v_val_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_val_276_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_val_276_);
lean_dec_ref(v___x_268_);
v___x_277_ = ((lean_object*)(l_Lean_isDeclMeta___closed__0));
v___x_278_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v___x_279_ = 0;
v___x_280_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_277_, v___x_278_, v_env_260_, v_val_276_, v___x_279_);
lean_dec(v_val_276_);
lean_dec_ref(v_env_260_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_array_get_size(v___x_280_);
v___x_283_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v___x_280_);
return v___x_265_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_sub(v___x_282_, v___x_284_);
v___x_286_ = lean_nat_dec_le(v___x_281_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v___x_285_);
lean_dec_ref(v___x_280_);
return v___x_265_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v_isModule_263_, v___x_280_, v___y_267_, v___x_281_, v___x_285_);
lean_dec_ref(v___x_280_);
return v___x_287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object* v_env_292_, lean_object* v_declName_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Lean_isDeclMeta(v_env_292_, v_declName_293_);
lean_dec(v_declName_293_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(uint8_t v___x_296_, lean_object* v_as_297_, lean_object* v_k_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_296_, v_as_297_, v_k_298_, v_x_299_, v_x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object* v___x_303_, lean_object* v_as_304_, lean_object* v_k_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
uint8_t v___x_534__boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v___x_534__boxed_309_ = lean_unbox(v___x_303_);
v_res_310_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v___x_534__boxed_309_, v_as_304_, v_k_305_, v_x_306_, v_x_307_, v_x_308_);
lean_dec(v_k_305_);
lean_dec_ref(v_as_304_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object* v_env_312_, lean_object* v_declName_313_){
_start:
{
uint8_t v___x_314_; 
lean_inc_ref(v_env_312_);
v___x_314_ = l_Lean_isDeclMeta(v_env_312_, v_declName_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v_toEnvExtension_316_; lean_object* v_asyncMode_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_315_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_316_ = lean_ctor_get(v___x_315_, 0);
v_asyncMode_317_ = lean_ctor_get(v_toEnvExtension_316_, 2);
v___x_318_ = lean_box(0);
v___x_319_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_315_, v_env_312_, v_declName_313_, v_asyncMode_317_, v___x_318_);
return v___x_319_;
}
else
{
lean_dec(v_declName_313_);
return v_env_312_;
}
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object* v_msg_327_){
_start:
{
lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___f_328_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__0));
v___f_329_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__1));
v___f_330_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__2));
v___f_331_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__3));
v___f_332_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__4));
v___f_333_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__5));
v___f_334_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__6));
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___f_328_);
lean_ctor_set(v___x_335_, 1, v___f_329_);
v___x_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___f_330_);
lean_ctor_set(v___x_336_, 2, v___f_331_);
lean_ctor_set(v___x_336_, 3, v___f_332_);
lean_ctor_set(v___x_336_, 4, v___f_333_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___f_334_);
v___x_338_ = 0;
v___x_339_ = lean_box(v___x_338_);
v___x_340_ = l_instInhabitedOfMonad___redArg(v___x_337_, v___x_339_);
v___x_341_ = lean_panic_fn_borrowed(v___x_340_, v_msg_327_);
lean_dec(v___x_340_);
v___x_342_ = lean_unbox(v___x_341_);
lean_dec(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object* v_msg_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_349_ = ((lean_object*)(l_Lean_getIRPhases___closed__2));
v___x_350_ = lean_unsigned_to_nat(14u);
v___x_351_ = lean_unsigned_to_nat(22u);
v___x_352_ = ((lean_object*)(l_Lean_getIRPhases___closed__1));
v___x_353_ = ((lean_object*)(l_Lean_getIRPhases___closed__0));
v___x_354_ = l_mkPanicMessageWithDecl(v___x_353_, v___x_352_, v___x_351_, v___x_350_, v___x_349_);
return v___x_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_getIRPhases(lean_object* v_env_355_, lean_object* v_declName_356_){
_start:
{
lean_object* v___x_357_; uint8_t v_isModule_358_; 
v___x_357_ = l_Lean_Environment_header(v_env_355_);
v_isModule_358_ = lean_ctor_get_uint8(v___x_357_, sizeof(void*)*7 + 4);
if (v_isModule_358_ == 0)
{
uint8_t v___x_359_; 
lean_dec_ref(v___x_357_);
lean_dec(v_declName_356_);
lean_dec_ref(v_env_355_);
v___x_359_ = 2;
return v___x_359_;
}
else
{
lean_object* v_modules_360_; lean_object* v___x_361_; 
v_modules_360_ = lean_ctor_get(v___x_357_, 3);
lean_inc_ref(v_modules_360_);
lean_dec_ref(v___x_357_);
v___x_361_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_355_, v_declName_356_);
if (lean_obj_tag(v___x_361_) == 0)
{
uint8_t v___x_362_; lean_object* v___x_363_; 
lean_dec_ref(v_modules_360_);
v___x_362_ = 0;
lean_inc(v_declName_356_);
lean_inc_ref(v_env_355_);
v___x_363_ = l_Lean_Environment_find_x3f(v_env_355_, v_declName_356_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
uint8_t v___x_364_; 
lean_dec(v_declName_356_);
lean_dec_ref(v_env_355_);
v___x_364_ = 2;
return v___x_364_;
}
else
{
lean_object* v_val_365_; uint8_t v___x_366_; 
v_val_365_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_365_);
lean_dec_ref(v___x_363_);
v___x_366_ = l_Lean_ConstantInfo_isCtor(v_val_365_);
lean_dec(v_val_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = l_Lean_isMarkedMeta(v_env_355_, v_declName_356_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 1;
return v___x_369_;
}
}
else
{
uint8_t v___x_370_; 
lean_dec(v_declName_356_);
lean_dec_ref(v_env_355_);
v___x_370_ = 2;
return v___x_370_;
}
}
}
else
{
lean_object* v_val_371_; uint8_t v___x_372_; 
v_val_371_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v___x_361_);
v___x_372_ = l_Lean_isMarkedMeta(v_env_355_, v_declName_356_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = lean_array_get_size(v_modules_360_);
v___x_374_ = lean_nat_dec_lt(v_val_371_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
lean_dec(v_val_371_);
lean_dec_ref(v_modules_360_);
v___x_375_ = lean_obj_once(&l_Lean_getIRPhases___closed__3, &l_Lean_getIRPhases___closed__3_once, _init_l_Lean_getIRPhases___closed__3);
v___x_376_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; uint8_t v_irPhases_378_; 
v___x_377_ = lean_array_fget(v_modules_360_, v_val_371_);
lean_dec(v_val_371_);
lean_dec_ref(v_modules_360_);
v_irPhases_378_ = lean_ctor_get_uint8(v___x_377_, sizeof(void*)*1);
lean_dec(v___x_377_);
return v_irPhases_378_;
}
}
else
{
uint8_t v___x_379_; 
lean_dec(v_val_371_);
lean_dec_ref(v_modules_360_);
v___x_379_ = 1;
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* v_env_380_, lean_object* v_declName_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Lean_getIRPhases(v_env_380_, v_declName_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_MetaAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_MetaAttr(builtin);
}
#ifdef __cplusplus
}
#endif
