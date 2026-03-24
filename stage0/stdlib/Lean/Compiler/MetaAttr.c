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
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declMetaExt"};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 84, 56, 43, 91, 46, 76, 198)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_toEnvExtension_42_);
v_asyncMode_43_ = lean_ctor_get(v_toEnvExtension_42_, 2);
lean_inc(v_asyncMode_43_);
lean_dec_ref(v_toEnvExtension_42_);
v___x_44_ = l_Lean_TagDeclarationExtension_isTagged(v___x_41_, v_env_39_, v_declName_40_, v_asyncMode_43_);
lean_dec(v_asyncMode_43_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_NameSet_empty;
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v_x_51_);
lean_dec_ref(v_x_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_es_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_array_mk(v_es_53_);
return v___x_54_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_x1_55_, lean_object* v_x2_56_){
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_x1_60_, lean_object* v_x2_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v_x1_60_, v_x2_61_);
lean_dec(v_x2_61_);
lean_dec(v_x1_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__0(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
return v_x_64_;
}
else
{
lean_object* v_head_66_; lean_object* v_tail_67_; lean_object* v___x_68_; 
v_head_66_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_head_66_);
v_tail_67_ = lean_ctor_get(v_x_65_, 1);
lean_inc(v_tail_67_);
lean_dec_ref(v_x_65_);
v___x_68_ = lean_array_push(v_x_64_, v_head_66_);
v_x_64_ = v___x_68_;
v_x_65_ = v_tail_67_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_71_, lean_object* v_lo_72_, lean_object* v_hi_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_lt(v_lo_72_, v_hi_73_);
if (v___x_74_ == 0)
{
lean_dec(v_lo_72_);
return v_as_71_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_fst_77_; lean_object* v_snd_78_; uint8_t v___x_79_; 
v___x_75_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_72_);
v___x_76_ = l_Array_qpartition___redArg(v_as_71_, v___x_75_, v_lo_72_, v_hi_73_);
v_fst_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_fst_77_);
v_snd_78_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_snd_78_);
lean_dec_ref(v___x_76_);
v___x_79_ = lean_nat_dec_le(v_hi_73_, v_fst_77_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_snd_78_, v_lo_72_, v_fst_77_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_fst_77_, v___x_81_);
lean_dec(v_fst_77_);
v_as_71_ = v___x_80_;
v_lo_72_ = v___x_82_;
goto _start;
}
else
{
lean_dec(v_fst_77_);
lean_dec(v_lo_72_);
return v_snd_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_84_, lean_object* v_lo_85_, lean_object* v_hi_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_as_84_, v_lo_85_, v_hi_86_);
lean_dec(v_hi_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v___x_88_, lean_object* v_env_89_, lean_object* v_s_90_, lean_object* v_entries_91_, uint8_t v_x_92_){
_start:
{
if (v_x_92_ == 2)
{
lean_object* v___x_93_; lean_object* v_decls_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_88_);
v_decls_94_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__0(v___x_93_, v_entries_91_);
v___x_95_ = lean_array_get_size(v_decls_94_);
v___x_96_ = lean_nat_dec_eq(v___x_95_, v___x_88_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___y_100_; uint8_t v___x_104_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_sub(v___x_95_, v___x_97_);
v___x_104_ = lean_nat_dec_le(v___x_88_, v___x_98_);
if (v___x_104_ == 0)
{
lean_dec(v___x_88_);
lean_inc(v___x_98_);
v___y_100_ = v___x_98_;
goto v___jp_99_;
}
else
{
v___y_100_ = v___x_88_;
goto v___jp_99_;
}
v___jp_99_:
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_le(v___y_100_, v___x_98_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec(v___x_98_);
lean_inc(v___y_100_);
v___x_102_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_decls_94_, v___y_100_, v___y_100_);
lean_dec(v___y_100_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_decls_94_, v___y_100_, v___x_98_);
lean_dec(v___x_98_);
return v___x_103_;
}
}
}
else
{
lean_dec(v___x_88_);
return v_decls_94_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_entries_91_);
v___x_105_ = lean_mk_empty_array_with_capacity(v___x_88_);
lean_dec(v___x_88_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v___x_106_, lean_object* v_env_107_, lean_object* v_s_108_, lean_object* v_entries_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_x_282__boxed_111_; lean_object* v_res_112_; 
v_x_282__boxed_111_ = lean_unbox(v_x_110_);
v_res_112_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v___x_106_, v_env_107_, v_s_108_, v_entries_109_, v_x_282__boxed_111_);
lean_dec(v_s_108_);
lean_dec_ref(v_env_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_));
v___x_140_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1(lean_object* v_n_143_, lean_object* v_as_144_, lean_object* v_lo_145_, lean_object* v_hi_146_, lean_object* v_w_147_, lean_object* v_hlo_148_, lean_object* v_hhi_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_as_144_, v_lo_145_, v_hi_146_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_151_, lean_object* v_as_152_, lean_object* v_lo_153_, lean_object* v_hi_154_, lean_object* v_w_155_, lean_object* v_hlo_156_, lean_object* v_hhi_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1(v_n_151_, v_as_152_, v_lo_153_, v_hi_154_, v_w_155_, v_hlo_156_, v_hhi_157_);
lean_dec(v_hi_154_);
lean_dec(v_n_151_);
return v_res_158_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(uint8_t v___x_159_, lean_object* v_as_160_, lean_object* v_k_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_m_166_; lean_object* v_a_167_; uint8_t v___x_168_; 
v___x_164_ = lean_nat_add(v_x_162_, v_x_163_);
v___x_165_ = lean_unsigned_to_nat(1u);
v_m_166_ = lean_nat_shiftr(v___x_164_, v___x_165_);
lean_dec(v___x_164_);
v_a_167_ = lean_array_fget_borrowed(v_as_160_, v_m_166_);
v___x_168_ = l_Lean_Name_quickLt(v_a_167_, v_k_161_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; 
lean_dec(v_x_163_);
v___x_169_ = l_Lean_Name_quickLt(v_k_161_, v_a_167_);
if (v___x_169_ == 0)
{
lean_dec(v_m_166_);
lean_dec(v_x_162_);
return v___x_159_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_nat_dec_eq(v_m_166_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_nat_sub(v_m_166_, v___x_165_);
lean_dec(v_m_166_);
v___x_173_ = lean_nat_dec_lt(v___x_172_, v_x_162_);
if (v___x_173_ == 0)
{
v_x_163_ = v___x_172_;
goto _start;
}
else
{
lean_dec(v___x_172_);
lean_dec(v_x_162_);
return v___x_168_;
}
}
else
{
lean_dec(v_m_166_);
lean_dec(v_x_162_);
return v___x_168_;
}
}
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
lean_dec(v_x_162_);
v___x_175_ = lean_nat_add(v_m_166_, v___x_165_);
lean_dec(v_m_166_);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_x_163_);
if (v___x_176_ == 0)
{
lean_dec(v___x_175_);
lean_dec(v_x_163_);
return v___x_176_;
}
else
{
v_x_162_ = v___x_175_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object* v___x_178_, lean_object* v_as_179_, lean_object* v_k_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
uint8_t v___x_435__boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v___x_435__boxed_183_ = lean_unbox(v___x_178_);
v_res_184_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_435__boxed_183_, v_as_179_, v_k_180_, v_x_181_, v_x_182_);
lean_dec(v_k_180_);
lean_dec_ref(v_as_179_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object* v_env_190_, lean_object* v_declName_191_){
_start:
{
lean_object* v___x_192_; uint8_t v_isModule_193_; 
v___x_192_ = l_Lean_Environment_header(v_env_190_);
v_isModule_193_ = lean_ctor_get_uint8(v___x_192_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_192_);
if (v_isModule_193_ == 0)
{
uint8_t v___x_194_; 
lean_dec_ref(v_env_190_);
v___x_194_ = 1;
return v___x_194_;
}
else
{
uint8_t v___x_195_; lean_object* v___y_197_; 
v___x_195_ = 0;
if (lean_obj_tag(v_declName_191_) == 1)
{
lean_object* v_pre_218_; lean_object* v_str_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_pre_218_ = lean_ctor_get(v_declName_191_, 0);
v_str_219_ = lean_ctor_get(v_declName_191_, 1);
v___x_220_ = ((lean_object*)(l_Lean_isDeclMeta___closed__1));
v___x_221_ = lean_string_dec_eq(v_str_219_, v___x_220_);
if (v___x_221_ == 0)
{
v___y_197_ = v_declName_191_;
goto v___jp_196_;
}
else
{
v___y_197_ = v_pre_218_;
goto v___jp_196_;
}
}
else
{
v___y_197_ = v_declName_191_;
goto v___jp_196_;
}
v___jp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_190_, v_declName_191_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v___x_199_; lean_object* v_toEnvExtension_200_; lean_object* v_asyncMode_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_199_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_toEnvExtension_200_);
v_asyncMode_201_ = lean_ctor_get(v_toEnvExtension_200_, 2);
lean_inc(v_asyncMode_201_);
lean_dec_ref(v_toEnvExtension_200_);
v___x_202_ = lean_box(1);
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_202_, v___x_199_, v_env_190_, v_asyncMode_201_, v___x_203_);
lean_dec(v_asyncMode_201_);
v___x_205_ = l_Lean_NameSet_contains(v___x_204_, v___y_197_);
lean_dec(v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_val_206_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v___x_198_);
v___x_207_ = ((lean_object*)(l_Lean_isDeclMeta___closed__0));
v___x_208_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v___x_209_ = 0;
v___x_210_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_207_, v___x_208_, v_env_190_, v_val_206_, v___x_209_);
lean_dec(v_val_206_);
lean_dec_ref(v_env_190_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_array_get_size(v___x_210_);
v___x_213_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___x_210_);
return v___x_195_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_sub(v___x_212_, v___x_214_);
v___x_216_ = lean_nat_dec_le(v___x_211_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v___x_215_);
lean_dec_ref(v___x_210_);
return v___x_195_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v_isModule_193_, v___x_210_, v___y_197_, v___x_211_, v___x_215_);
lean_dec_ref(v___x_210_);
return v___x_217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object* v_env_222_, lean_object* v_declName_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_isDeclMeta(v_env_222_, v_declName_223_);
lean_dec(v_declName_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(uint8_t v___x_226_, lean_object* v_as_227_, lean_object* v_k_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_226_, v_as_227_, v_k_228_, v_x_229_, v_x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object* v___x_233_, lean_object* v_as_234_, lean_object* v_k_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint8_t v___x_534__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v___x_534__boxed_239_ = lean_unbox(v___x_233_);
v_res_240_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v___x_534__boxed_239_, v_as_234_, v_k_235_, v_x_236_, v_x_237_, v_x_238_);
lean_dec(v_k_235_);
lean_dec_ref(v_as_234_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object* v_env_242_, lean_object* v_declName_243_){
_start:
{
uint8_t v___x_244_; 
lean_inc_ref(v_env_242_);
v___x_244_ = l_Lean_isDeclMeta(v_env_242_, v_declName_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v_toEnvExtension_246_; lean_object* v_asyncMode_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_toEnvExtension_246_);
v_asyncMode_247_ = lean_ctor_get(v_toEnvExtension_246_, 2);
lean_inc(v_asyncMode_247_);
lean_dec_ref(v_toEnvExtension_246_);
v___x_248_ = lean_box(0);
v___x_249_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_245_, v_env_242_, v_declName_243_, v_asyncMode_247_, v___x_248_);
lean_dec(v_asyncMode_247_);
return v___x_249_;
}
else
{
lean_dec(v_declName_243_);
return v_env_242_;
}
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object* v_msg_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___f_258_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__0));
v___f_259_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__1));
v___f_260_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__2));
v___f_261_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__3));
v___f_262_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__4));
v___f_263_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__5));
v___f_264_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__6));
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___f_258_);
lean_ctor_set(v___x_265_, 1, v___f_259_);
v___x_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___f_260_);
lean_ctor_set(v___x_266_, 2, v___f_261_);
lean_ctor_set(v___x_266_, 3, v___f_262_);
lean_ctor_set(v___x_266_, 4, v___f_263_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___f_264_);
v___x_268_ = 0;
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = l_instInhabitedOfMonad___redArg(v___x_267_, v___x_269_);
v___x_271_ = lean_panic_fn(v___x_270_, v_msg_257_);
v___x_272_ = lean_unbox(v___x_271_);
lean_dec(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object* v_msg_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = ((lean_object*)(l_Lean_getIRPhases___closed__2));
v___x_280_ = lean_unsigned_to_nat(14u);
v___x_281_ = lean_unsigned_to_nat(22u);
v___x_282_ = ((lean_object*)(l_Lean_getIRPhases___closed__1));
v___x_283_ = ((lean_object*)(l_Lean_getIRPhases___closed__0));
v___x_284_ = l_mkPanicMessageWithDecl(v___x_283_, v___x_282_, v___x_281_, v___x_280_, v___x_279_);
return v___x_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_getIRPhases(lean_object* v_env_285_, lean_object* v_declName_286_){
_start:
{
lean_object* v___x_287_; uint8_t v_isModule_288_; 
v___x_287_ = l_Lean_Environment_header(v_env_285_);
v_isModule_288_ = lean_ctor_get_uint8(v___x_287_, sizeof(void*)*7 + 4);
if (v_isModule_288_ == 0)
{
uint8_t v___x_289_; 
lean_dec_ref(v___x_287_);
lean_dec(v_declName_286_);
lean_dec_ref(v_env_285_);
v___x_289_ = 2;
return v___x_289_;
}
else
{
lean_object* v_modules_290_; lean_object* v___x_291_; 
v_modules_290_ = lean_ctor_get(v___x_287_, 3);
lean_inc_ref(v_modules_290_);
lean_dec_ref(v___x_287_);
v___x_291_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_285_, v_declName_286_);
if (lean_obj_tag(v___x_291_) == 0)
{
uint8_t v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v_modules_290_);
v___x_292_ = 0;
lean_inc(v_declName_286_);
lean_inc_ref(v_env_285_);
v___x_293_ = l_Lean_Environment_find_x3f(v_env_285_, v_declName_286_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
uint8_t v___x_294_; 
lean_dec(v_declName_286_);
lean_dec_ref(v_env_285_);
v___x_294_ = 2;
return v___x_294_;
}
else
{
lean_object* v_val_295_; uint8_t v___x_296_; 
v_val_295_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_295_);
lean_dec_ref(v___x_293_);
v___x_296_ = l_Lean_ConstantInfo_isCtor(v_val_295_);
lean_dec(v_val_295_);
if (v___x_296_ == 0)
{
uint8_t v___x_297_; 
v___x_297_ = l_Lean_isMarkedMeta(v_env_285_, v_declName_286_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
}
else
{
uint8_t v___x_300_; 
lean_dec(v_declName_286_);
lean_dec_ref(v_env_285_);
v___x_300_ = 2;
return v___x_300_;
}
}
}
else
{
lean_object* v_val_301_; uint8_t v___x_302_; 
v_val_301_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_301_);
lean_dec_ref(v___x_291_);
v___x_302_ = l_Lean_isMarkedMeta(v_env_285_, v_declName_286_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_array_get_size(v_modules_290_);
v___x_304_ = lean_nat_dec_lt(v_val_301_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
lean_dec(v_val_301_);
lean_dec_ref(v_modules_290_);
v___x_305_ = lean_obj_once(&l_Lean_getIRPhases___closed__3, &l_Lean_getIRPhases___closed__3_once, _init_l_Lean_getIRPhases___closed__3);
v___x_306_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_305_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; uint8_t v_irPhases_308_; 
v___x_307_ = lean_array_fget(v_modules_290_, v_val_301_);
lean_dec(v_val_301_);
lean_dec_ref(v_modules_290_);
v_irPhases_308_ = lean_ctor_get_uint8(v___x_307_, sizeof(void*)*1);
lean_dec(v___x_307_);
return v_irPhases_308_;
}
}
else
{
uint8_t v___x_309_; 
lean_dec(v_val_301_);
lean_dec_ref(v_modules_290_);
v___x_309_ = 1;
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* v_env_310_, lean_object* v_declName_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_getIRPhases(v_env_310_, v_declName_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
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
res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_();
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
