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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isDeclMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_isDeclMeta___closed__0 = (const lean_object*)&l_Lean_isDeclMeta___closed__0_value;
static const lean_string_object l_Lean_isDeclMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_isDeclMeta___closed__1 = (const lean_object*)&l_Lean_isDeclMeta___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = l_Lean_NameSet_contains(v_x1_55_, v_x2_56_);
v___x_58_ = lean_bool_not(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_x1_59_, lean_object* v_x2_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x1_59_, v_x2_60_);
lean_dec(v_x2_60_);
lean_dec(v_x1_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_hi_63_, lean_object* v_pivot_64_, lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_k_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_nat_dec_lt(v_k_67_, v_hi_63_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_k_67_);
v___x_69_ = lean_array_fswap(v_as_65_, v_i_66_, v_hi_63_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_i_66_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_array_fget_borrowed(v_as_65_, v_k_67_);
v___x_72_ = l_Lean_Name_quickLt(v___x_71_, v_pivot_64_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_k_67_, v___x_73_);
lean_dec(v_k_67_);
v_k_67_ = v___x_74_;
goto _start;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_array_fswap(v_as_65_, v_i_66_, v_k_67_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_i_66_, v___x_77_);
lean_dec(v_i_66_);
v___x_79_ = lean_nat_add(v_k_67_, v___x_77_);
lean_dec(v_k_67_);
v_as_65_ = v___x_76_;
v_i_66_ = v___x_78_;
v_k_67_ = v___x_79_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object* v_hi_81_, lean_object* v_pivot_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_k_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_81_, v_pivot_82_, v_as_83_, v_i_84_, v_k_85_);
lean_dec(v_pivot_82_);
lean_dec(v_hi_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_87_, lean_object* v_as_88_, lean_object* v_lo_89_, lean_object* v_hi_90_){
_start:
{
lean_object* v___y_92_; uint8_t v___x_102_; 
v___x_102_ = lean_nat_dec_lt(v_lo_89_, v_hi_90_);
if (v___x_102_ == 0)
{
lean_dec(v_lo_89_);
return v_as_88_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_mid_105_; lean_object* v___y_107_; lean_object* v___y_113_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_103_ = lean_nat_add(v_lo_89_, v_hi_90_);
v___x_104_ = lean_unsigned_to_nat(1u);
v_mid_105_ = lean_nat_shiftr(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v___x_118_ = lean_array_fget_borrowed(v_as_88_, v_mid_105_);
v___x_119_ = lean_array_fget_borrowed(v_as_88_, v_lo_89_);
v___x_120_ = l_Lean_Name_quickLt(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
v___y_113_ = v_as_88_;
goto v___jp_112_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_array_fswap(v_as_88_, v_lo_89_, v_mid_105_);
v___y_113_ = v___x_121_;
goto v___jp_112_;
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = lean_array_fget_borrowed(v___y_107_, v_mid_105_);
v___x_109_ = lean_array_fget_borrowed(v___y_107_, v_hi_90_);
v___x_110_ = l_Lean_Name_quickLt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec(v_mid_105_);
v___y_92_ = v___y_107_;
goto v___jp_91_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_array_fswap(v___y_107_, v_mid_105_, v_hi_90_);
lean_dec(v_mid_105_);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
}
v___jp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_array_fget_borrowed(v___y_113_, v_hi_90_);
v___x_115_ = lean_array_fget_borrowed(v___y_113_, v_lo_89_);
v___x_116_ = l_Lean_Name_quickLt(v___x_114_, v___x_115_);
if (v___x_116_ == 0)
{
v___y_107_ = v___y_113_;
goto v___jp_106_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_array_fswap(v___y_113_, v_lo_89_, v_hi_90_);
v___y_107_ = v___x_117_;
goto v___jp_106_;
}
}
}
v___jp_91_:
{
lean_object* v_pivot_93_; lean_object* v___x_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; uint8_t v___x_97_; 
v_pivot_93_ = lean_array_fget(v___y_92_, v_hi_90_);
lean_inc_n(v_lo_89_, 2);
v___x_94_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_90_, v_pivot_93_, v___y_92_, v_lo_89_, v_lo_89_);
lean_dec(v_pivot_93_);
v_fst_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_fst_95_);
v_snd_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_snd_96_);
lean_dec_ref(v___x_94_);
v___x_97_ = lean_nat_dec_le(v_hi_90_, v_fst_95_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_87_, v_snd_96_, v_lo_89_, v_fst_95_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_fst_95_, v___x_99_);
lean_dec(v_fst_95_);
v_as_88_ = v___x_98_;
v_lo_89_ = v___x_100_;
goto _start;
}
else
{
lean_dec(v_fst_95_);
lean_dec(v_lo_89_);
return v_snd_96_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_122_, lean_object* v_as_123_, lean_object* v_lo_124_, lean_object* v_hi_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_122_, v_as_123_, v_lo_124_, v_hi_125_);
lean_dec(v_hi_125_);
lean_dec(v_n_122_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
return v_x_127_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_131_; 
v_head_129_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_head_129_);
v_tail_130_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_tail_130_);
lean_dec_ref_known(v_x_128_, 2);
v___x_131_ = lean_array_push(v_x_127_, v_head_129_);
v_x_127_ = v___x_131_;
v_x_128_ = v_tail_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v___x_133_, lean_object* v_env_134_, lean_object* v_s_135_, lean_object* v_entries_136_){
_start:
{
lean_object* v___x_137_; lean_object* v_decls_138_; lean_object* v___x_139_; lean_object* v___y_141_; lean_object* v___y_142_; uint8_t v___x_145_; 
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_133_);
lean_inc_ref(v___x_137_);
v_decls_138_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(v___x_137_, v_entries_136_);
v___x_139_ = lean_array_get_size(v_decls_138_);
v___x_145_ = lean_nat_dec_eq(v___x_139_, v___x_133_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___y_149_; uint8_t v___x_151_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_sub(v___x_139_, v___x_146_);
v___x_151_ = lean_nat_dec_le(v___x_133_, v___x_147_);
if (v___x_151_ == 0)
{
lean_dec(v___x_133_);
lean_inc(v___x_147_);
v___y_149_ = v___x_147_;
goto v___jp_148_;
}
else
{
v___y_149_ = v___x_133_;
goto v___jp_148_;
}
v___jp_148_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_le(v___y_149_, v___x_147_);
if (v___x_150_ == 0)
{
lean_dec(v___x_147_);
lean_inc(v___y_149_);
v___y_141_ = v___y_149_;
v___y_142_ = v___y_149_;
goto v___jp_140_;
}
else
{
v___y_141_ = v___y_149_;
v___y_142_ = v___x_147_;
goto v___jp_140_;
}
}
}
else
{
lean_object* v___x_152_; 
lean_dec(v___x_133_);
lean_inc_ref(v___x_137_);
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_137_);
lean_ctor_set(v___x_152_, 1, v___x_137_);
lean_ctor_set(v___x_152_, 2, v_decls_138_);
return v___x_152_;
}
v___jp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v___x_139_, v_decls_138_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_inc_ref(v___x_137_);
v___x_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_137_);
lean_ctor_set(v___x_144_, 1, v___x_137_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v___x_153_, lean_object* v_env_154_, lean_object* v_s_155_, lean_object* v_entries_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v___x_153_, v_env_154_, v_s_155_, v_entries_156_);
lean_dec(v_s_155_);
lean_dec_ref(v_env_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_));
v___x_185_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(lean_object* v_n_188_, lean_object* v_as_189_, lean_object* v_lo_190_, lean_object* v_hi_191_, lean_object* v_w_192_, lean_object* v_hlo_193_, lean_object* v_hhi_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_188_, v_as_189_, v_lo_190_, v_hi_191_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_196_, lean_object* v_as_197_, lean_object* v_lo_198_, lean_object* v_hi_199_, lean_object* v_w_200_, lean_object* v_hlo_201_, lean_object* v_hhi_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(v_n_196_, v_as_197_, v_lo_198_, v_hi_199_, v_w_200_, v_hlo_201_, v_hhi_202_);
lean_dec(v_hi_199_);
lean_dec(v_n_196_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_n_204_, lean_object* v_lo_205_, lean_object* v_hi_206_, lean_object* v_hhi_207_, lean_object* v_pivot_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_k_211_, lean_object* v_ilo_212_, lean_object* v_ik_213_, lean_object* v_w_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_206_, v_pivot_208_, v_as_209_, v_i_210_, v_k_211_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_n_216_, lean_object* v_lo_217_, lean_object* v_hi_218_, lean_object* v_hhi_219_, lean_object* v_pivot_220_, lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_k_223_, lean_object* v_ilo_224_, lean_object* v_ik_225_, lean_object* v_w_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(v_n_216_, v_lo_217_, v_hi_218_, v_hhi_219_, v_pivot_220_, v_as_221_, v_i_222_, v_k_223_, v_ilo_224_, v_ik_225_, v_w_226_);
lean_dec(v_pivot_220_);
lean_dec(v_hi_218_);
lean_dec(v_lo_217_);
lean_dec(v_n_216_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(lean_object* v_as_228_, lean_object* v_k_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_m_234_; lean_object* v_a_235_; uint8_t v___x_236_; 
v___x_232_ = lean_nat_add(v_x_230_, v_x_231_);
v___x_233_ = lean_unsigned_to_nat(1u);
v_m_234_ = lean_nat_shiftr(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
v_a_235_ = lean_array_fget_borrowed(v_as_228_, v_m_234_);
v___x_236_ = l_Lean_Name_quickLt(v_a_235_, v_k_229_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; 
lean_dec(v_x_231_);
v___x_237_ = l_Lean_Name_quickLt(v_k_229_, v_a_235_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
lean_dec(v_m_234_);
lean_dec(v_x_230_);
v___x_238_ = 1;
return v___x_238_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_nat_dec_eq(v_m_234_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_nat_sub(v_m_234_, v___x_233_);
lean_dec(v_m_234_);
v___x_242_ = lean_nat_dec_lt(v___x_241_, v_x_230_);
if (v___x_242_ == 0)
{
v_x_231_ = v___x_241_;
goto _start;
}
else
{
lean_dec(v___x_241_);
lean_dec(v_x_230_);
return v___x_236_;
}
}
else
{
lean_dec(v_m_234_);
lean_dec(v_x_230_);
return v___x_236_;
}
}
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
lean_dec(v_x_230_);
v___x_244_ = lean_nat_add(v_m_234_, v___x_233_);
lean_dec(v_m_234_);
v___x_245_ = lean_nat_dec_le(v___x_244_, v_x_231_);
if (v___x_245_ == 0)
{
lean_dec(v___x_244_);
lean_dec(v_x_231_);
return v___x_245_;
}
else
{
v_x_230_ = v___x_244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object* v_as_247_, lean_object* v_k_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v_as_247_, v_k_248_, v_x_249_, v_x_250_);
lean_dec(v_k_248_);
lean_dec_ref(v_as_247_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object* v_env_257_, lean_object* v_declName_258_){
_start:
{
lean_object* v___x_259_; uint8_t v_isModule_260_; uint8_t v___x_261_; lean_object* v___y_263_; 
v___x_259_ = l_Lean_Environment_header(v_env_257_);
v_isModule_260_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_259_);
v___x_261_ = lean_bool_not(v_isModule_260_);
if (v___x_261_ == 0)
{
if (lean_obj_tag(v_declName_258_) == 1)
{
lean_object* v_pre_284_; lean_object* v_str_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_pre_284_ = lean_ctor_get(v_declName_258_, 0);
v_str_285_ = lean_ctor_get(v_declName_258_, 1);
v___x_286_ = ((lean_object*)(l_Lean_isDeclMeta___closed__1));
v___x_287_ = lean_string_dec_eq(v_str_285_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_263_ = v_declName_258_;
goto v___jp_262_;
}
else
{
v___y_263_ = v_pre_284_;
goto v___jp_262_;
}
}
else
{
v___y_263_ = v_declName_258_;
goto v___jp_262_;
}
}
else
{
lean_dec_ref(v_env_257_);
return v___x_261_;
}
v___jp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_257_, v_declName_258_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v_toEnvExtension_266_; lean_object* v_asyncMode_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_265_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_266_ = lean_ctor_get(v___x_265_, 0);
v_asyncMode_267_ = lean_ctor_get(v_toEnvExtension_266_, 2);
v___x_268_ = lean_box(1);
v___x_269_ = lean_box(0);
v___x_270_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_268_, v___x_265_, v_env_257_, v_asyncMode_267_, v___x_269_);
v___x_271_ = l_Lean_NameSet_contains(v___x_270_, v___y_263_);
lean_dec(v___x_270_);
return v___x_271_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_val_272_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v___x_264_, 1);
v___x_273_ = ((lean_object*)(l_Lean_isDeclMeta___closed__0));
v___x_274_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v___x_275_ = 0;
v___x_276_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_273_, v___x_274_, v_env_257_, v_val_272_, v___x_275_);
lean_dec(v_val_272_);
lean_dec_ref(v_env_257_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_array_get_size(v___x_276_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v___x_276_);
return v___x_261_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_sub(v___x_278_, v___x_280_);
v___x_282_ = lean_nat_dec_le(v___x_277_, v___x_281_);
if (v___x_282_ == 0)
{
lean_dec(v___x_281_);
lean_dec_ref(v___x_276_);
return v___x_261_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_276_, v___y_263_, v___x_277_, v___x_281_);
lean_dec_ref(v___x_276_);
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object* v_env_288_, lean_object* v_declName_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Lean_isDeclMeta(v_env_288_, v_declName_289_);
lean_dec(v_declName_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(lean_object* v_as_292_, lean_object* v_k_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v_as_292_, v_k_293_, v_x_294_, v_x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object* v_as_298_, lean_object* v_k_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v_as_298_, v_k_299_, v_x_300_, v_x_301_, v_x_302_);
lean_dec(v_k_299_);
lean_dec_ref(v_as_298_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object* v_env_305_, lean_object* v_declName_306_){
_start:
{
uint8_t v___x_307_; 
lean_inc_ref(v_env_305_);
v___x_307_ = l_Lean_isDeclMeta(v_env_305_, v_declName_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v_toEnvExtension_309_; lean_object* v_asyncMode_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_309_ = lean_ctor_get(v___x_308_, 0);
v_asyncMode_310_ = lean_ctor_get(v_toEnvExtension_309_, 2);
v___x_311_ = lean_box(0);
v___x_312_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_308_, v_env_305_, v_declName_306_, v_asyncMode_310_, v___x_311_);
return v___x_312_;
}
else
{
lean_dec(v_declName_306_);
return v_env_305_;
}
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object* v_msg_320_){
_start:
{
lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___f_321_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__0));
v___f_322_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__1));
v___f_323_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__2));
v___f_324_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__3));
v___f_325_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__4));
v___f_326_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__5));
v___f_327_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__6));
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___f_321_);
lean_ctor_set(v___x_328_, 1, v___f_322_);
v___x_329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___f_323_);
lean_ctor_set(v___x_329_, 2, v___f_324_);
lean_ctor_set(v___x_329_, 3, v___f_325_);
lean_ctor_set(v___x_329_, 4, v___f_326_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___f_327_);
v___x_331_ = 0;
v___x_332_ = lean_box(v___x_331_);
v___x_333_ = l_instInhabitedOfMonad___redArg(v___x_330_, v___x_332_);
v___x_334_ = lean_panic_fn_borrowed(v___x_333_, v_msg_320_);
lean_dec(v___x_333_);
v___x_335_ = lean_unbox(v___x_334_);
lean_dec(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object* v_msg_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((lean_object*)(l_Lean_getIRPhases___closed__2));
v___x_343_ = lean_unsigned_to_nat(14u);
v___x_344_ = lean_unsigned_to_nat(22u);
v___x_345_ = ((lean_object*)(l_Lean_getIRPhases___closed__1));
v___x_346_ = ((lean_object*)(l_Lean_getIRPhases___closed__0));
v___x_347_ = l_mkPanicMessageWithDecl(v___x_346_, v___x_345_, v___x_344_, v___x_343_, v___x_342_);
return v___x_347_;
}
}
LEAN_EXPORT uint8_t l_Lean_getIRPhases(lean_object* v_env_348_, lean_object* v_declName_349_){
_start:
{
lean_object* v___x_350_; uint8_t v_isModule_351_; lean_object* v_modules_352_; uint8_t v___x_353_; 
v___x_350_ = l_Lean_Environment_header(v_env_348_);
v_isModule_351_ = lean_ctor_get_uint8(v___x_350_, sizeof(void*)*7 + 4);
v_modules_352_ = lean_ctor_get(v___x_350_, 3);
lean_inc_ref(v_modules_352_);
lean_dec_ref(v___x_350_);
v___x_353_ = lean_bool_not(v_isModule_351_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_348_, v_declName_349_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v_modules_352_);
lean_inc(v_declName_349_);
lean_inc_ref(v_env_348_);
v___x_355_ = l_Lean_Environment_find_x3f(v_env_348_, v_declName_349_, v___x_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
uint8_t v___x_356_; 
lean_dec(v_declName_349_);
lean_dec_ref(v_env_348_);
v___x_356_ = 2;
return v___x_356_;
}
else
{
lean_object* v_val_357_; uint8_t v___x_358_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_355_, 1);
v___x_358_ = l_Lean_ConstantInfo_isCtor(v_val_357_);
lean_dec(v_val_357_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_isMarkedMeta(v_env_348_, v_declName_349_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 0;
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 1;
return v___x_361_;
}
}
else
{
uint8_t v___x_362_; 
lean_dec(v_declName_349_);
lean_dec_ref(v_env_348_);
v___x_362_ = 2;
return v___x_362_;
}
}
}
else
{
lean_object* v_val_363_; uint8_t v___x_364_; 
v_val_363_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v___x_354_, 1);
v___x_364_ = l_Lean_isMarkedMeta(v_env_348_, v_declName_349_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_array_get_size(v_modules_352_);
v___x_366_ = lean_nat_dec_lt(v_val_363_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; uint8_t v___x_368_; 
lean_dec(v_val_363_);
lean_dec_ref(v_modules_352_);
v___x_367_ = lean_obj_once(&l_Lean_getIRPhases___closed__3, &l_Lean_getIRPhases___closed__3_once, _init_l_Lean_getIRPhases___closed__3);
v___x_368_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_367_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v_irPhases_370_; 
v___x_369_ = lean_array_fget(v_modules_352_, v_val_363_);
lean_dec(v_val_363_);
lean_dec_ref(v_modules_352_);
v_irPhases_370_ = lean_ctor_get_uint8(v___x_369_, sizeof(void*)*1);
lean_dec(v___x_369_);
return v_irPhases_370_;
}
}
else
{
uint8_t v___x_371_; 
lean_dec(v_val_363_);
lean_dec_ref(v_modules_352_);
v___x_371_ = 1;
return v___x_371_;
}
}
}
else
{
uint8_t v___x_372_; 
lean_dec_ref(v_modules_352_);
lean_dec(v_declName_349_);
lean_dec_ref(v_env_348_);
v___x_372_ = 2;
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* v_env_373_, lean_object* v_declName_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_getIRPhases(v_env_373_, v_declName_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
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
