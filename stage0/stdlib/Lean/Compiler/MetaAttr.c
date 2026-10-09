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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isDeclMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_isDeclMeta___closed__0 = (const lean_object*)&l_Lean_isDeclMeta___closed__0_value;
static const lean_string_object l_Lean_isDeclMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_isDeclMeta___closed__1 = (const lean_object*)&l_Lean_isDeclMeta___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setDeclMeta___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_30_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_));
v___x_31_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_));
v___x_32_ = 0;
v___x_33_ = l_Lean_mkTagDeclarationExtension(v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_34_;
v_res_34_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2____boxed(lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_();
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_markMeta(lean_object* v_env_37_, lean_object* v_declName_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v___x_40_ = l_Lean_TagDeclarationExtension_tag(v___x_39_, v_env_37_, v_declName_38_);
return v___x_40_;
}
}
uint8_t l_Lean_isMarkedMeta(lean_object* v_env_41_, lean_object* v_declName_42_){
_start:
{
lean_object* v___x_43_; lean_object* v_toEnvExtension_44_; lean_object* v_asyncMode_45_; uint8_t v___x_46_; 
v___x_43_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v_toEnvExtension_44_ = lean_ctor_get(v___x_43_, 0);
v_asyncMode_45_ = lean_ctor_get(v_toEnvExtension_44_, 2);
v___x_46_ = l_Lean_TagDeclarationExtension_isTagged(v___x_43_, v_env_41_, v_declName_42_, v_asyncMode_45_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lean_isMarkedMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_41_ = stack[0].m_obj;
lean_object* v_declName_42_ = stack[1].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Lean_isMarkedMeta(v_env_41_, v_declName_42_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_isMarkedMeta___boxed(lean_object* v_env_48_, lean_object* v_declName_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_isMarkedMeta(v_env_48_, v_declName_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_NameSet_empty;
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x_54_);
lean_dec_ref(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_es_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_array_mk(v_es_56_);
return v___x_57_;
}
}
uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v_x1_58_, lean_object* v_x2_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_NameSet_contains(v_x1_58_, v_x2_59_);
if (v___x_60_ == 0)
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
else
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_58_ = stack[0].m_obj;
lean_object* v_x2_59_ = stack[1].m_obj;
uint8_t v_res_63_;
v_res_63_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x1_58_, v_x2_59_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_x1_64_, lean_object* v_x2_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v_x1_64_, v_x2_65_);
lean_dec(v_x2_65_);
lean_dec(v_x1_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(lean_object* v_hi_68_, lean_object* v_pivot_69_, lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_k_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_nat_dec_lt(v_k_72_, v_hi_68_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_k_72_);
v___x_74_ = lean_array_fswap(v_as_70_, v_i_71_, v_hi_68_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_i_71_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_array_fget_borrowed(v_as_70_, v_k_72_);
v___x_77_ = l_Lean_Name_quickLt(v___x_76_, v_pivot_69_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_k_72_, v___x_78_);
lean_dec(v_k_72_);
v_k_72_ = v___x_79_;
goto _start;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = lean_array_fswap(v_as_70_, v_i_71_, v_k_72_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_i_71_, v___x_82_);
lean_dec(v_i_71_);
v___x_84_ = lean_nat_add(v_k_72_, v___x_82_);
lean_dec(v_k_72_);
v_as_70_ = v___x_81_;
v_i_71_ = v___x_83_;
v_k_72_ = v___x_84_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(lean_object* v_hi_86_, lean_object* v_pivot_87_, lean_object* v_as_88_, lean_object* v_i_89_, lean_object* v_k_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_86_, v_pivot_87_, v_as_88_, v_i_89_, v_k_90_);
lean_dec(v_pivot_87_);
lean_dec(v_hi_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_92_, lean_object* v_as_93_, lean_object* v_lo_94_, lean_object* v_hi_95_){
_start:
{
lean_object* v___y_97_; uint8_t v___x_107_; 
v___x_107_ = lean_nat_dec_lt(v_lo_94_, v_hi_95_);
if (v___x_107_ == 0)
{
lean_dec(v_lo_94_);
return v_as_93_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_mid_110_; lean_object* v___y_112_; lean_object* v___y_118_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_108_ = lean_nat_add(v_lo_94_, v_hi_95_);
v___x_109_ = lean_unsigned_to_nat(1u);
v_mid_110_ = lean_nat_shiftr(v___x_108_, v___x_109_);
lean_dec(v___x_108_);
v___x_123_ = lean_array_fget_borrowed(v_as_93_, v_mid_110_);
v___x_124_ = lean_array_fget_borrowed(v_as_93_, v_lo_94_);
v___x_125_ = l_Lean_Name_quickLt(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
v___y_118_ = v_as_93_;
goto v___jp_117_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_array_fswap(v_as_93_, v_lo_94_, v_mid_110_);
v___y_118_ = v___x_126_;
goto v___jp_117_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_array_fget_borrowed(v___y_112_, v_mid_110_);
v___x_114_ = lean_array_fget_borrowed(v___y_112_, v_hi_95_);
v___x_115_ = l_Lean_Name_quickLt(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec(v_mid_110_);
v___y_97_ = v___y_112_;
goto v___jp_96_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_array_fswap(v___y_112_, v_mid_110_, v_hi_95_);
lean_dec(v_mid_110_);
v___y_97_ = v___x_116_;
goto v___jp_96_;
}
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_array_fget_borrowed(v___y_118_, v_hi_95_);
v___x_120_ = lean_array_fget_borrowed(v___y_118_, v_lo_94_);
v___x_121_ = l_Lean_Name_quickLt(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
v___y_112_ = v___y_118_;
goto v___jp_111_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = lean_array_fswap(v___y_118_, v_lo_94_, v_hi_95_);
v___y_112_ = v___x_122_;
goto v___jp_111_;
}
}
}
v___jp_96_:
{
lean_object* v_pivot_98_; lean_object* v___x_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; uint8_t v___x_102_; 
v_pivot_98_ = lean_array_fget(v___y_97_, v_hi_95_);
lean_inc_n(v_lo_94_, 2);
v___x_99_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_95_, v_pivot_98_, v___y_97_, v_lo_94_, v_lo_94_);
lean_dec(v_pivot_98_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_fst_100_);
v_snd_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___x_99_);
v___x_102_ = lean_nat_dec_le(v_hi_95_, v_fst_100_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_92_, v_snd_101_, v_lo_94_, v_fst_100_);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_fst_100_, v___x_104_);
lean_dec(v_fst_100_);
v_as_93_ = v___x_103_;
v_lo_94_ = v___x_105_;
goto _start;
}
else
{
lean_dec(v_fst_100_);
lean_dec(v_lo_94_);
return v_snd_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_127_, lean_object* v_as_128_, lean_object* v_lo_129_, lean_object* v_hi_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_127_, v_as_128_, v_lo_129_, v_hi_130_);
lean_dec(v_hi_130_);
lean_dec(v_n_127_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
return v_x_132_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v___x_136_; 
v_head_134_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_head_134_);
v_tail_135_ = lean_ctor_get(v_x_133_, 1);
lean_inc(v_tail_135_);
lean_dec_ref_known(v_x_133_, 2);
v___x_136_ = lean_array_push(v_x_132_, v_head_134_);
v_x_132_ = v___x_136_;
v_x_133_ = v_tail_135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(lean_object* v___x_138_, lean_object* v_env_139_, lean_object* v_s_140_, lean_object* v_entries_141_){
_start:
{
lean_object* v___x_142_; lean_object* v_decls_143_; lean_object* v___x_144_; lean_object* v___y_146_; lean_object* v___y_147_; uint8_t v___x_150_; 
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_138_);
lean_inc_ref(v___x_142_);
v_decls_143_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__0(v___x_142_, v_entries_141_);
v___x_144_ = lean_array_get_size(v_decls_143_);
v___x_150_ = lean_nat_dec_eq(v___x_144_, v___x_138_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___y_154_; uint8_t v___x_156_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_sub(v___x_144_, v___x_151_);
v___x_156_ = lean_nat_dec_le(v___x_138_, v___x_152_);
if (v___x_156_ == 0)
{
lean_dec(v___x_138_);
lean_inc(v___x_152_);
v___y_154_ = v___x_152_;
goto v___jp_153_;
}
else
{
v___y_154_ = v___x_138_;
goto v___jp_153_;
}
v___jp_153_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_le(v___y_154_, v___x_152_);
if (v___x_155_ == 0)
{
lean_dec(v___x_152_);
lean_inc(v___y_154_);
v___y_146_ = v___y_154_;
v___y_147_ = v___y_154_;
goto v___jp_145_;
}
else
{
v___y_146_ = v___y_154_;
v___y_147_ = v___x_152_;
goto v___jp_145_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v___x_138_);
lean_inc_ref(v___x_142_);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_142_);
lean_ctor_set(v___x_157_, 1, v___x_142_);
lean_ctor_set(v___x_157_, 2, v_decls_143_);
return v___x_157_;
}
v___jp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v___x_144_, v_decls_143_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_inc_ref(v___x_142_);
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_142_);
lean_ctor_set(v___x_149_, 1, v___x_142_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v___x_158_, lean_object* v_env_159_, lean_object* v_s_160_, lean_object* v_entries_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(v___x_158_, v_env_159_, v_s_160_, v_entries_161_);
lean_dec(v_s_160_);
lean_dec_ref(v_env_159_);
return v_res_162_;
}
}
lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_));
v___x_191_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_192_;
v_res_192_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2____boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2_();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(lean_object* v_n_195_, lean_object* v_as_196_, lean_object* v_lo_197_, lean_object* v_hi_198_, lean_object* v_w_199_, lean_object* v_hlo_200_, lean_object* v_hhi_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___redArg(v_n_195_, v_as_196_, v_lo_197_, v_hi_198_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_203_, lean_object* v_as_204_, lean_object* v_lo_205_, lean_object* v_hi_206_, lean_object* v_w_207_, lean_object* v_hlo_208_, lean_object* v_hhi_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1(v_n_203_, v_as_204_, v_lo_205_, v_hi_206_, v_w_207_, v_hlo_208_, v_hhi_209_);
lean_dec(v_hi_206_);
lean_dec(v_n_203_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_n_211_, lean_object* v_lo_212_, lean_object* v_hi_213_, lean_object* v_hhi_214_, lean_object* v_pivot_215_, lean_object* v_as_216_, lean_object* v_i_217_, lean_object* v_k_218_, lean_object* v_ilo_219_, lean_object* v_ik_220_, lean_object* v_w_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___redArg(v_hi_213_, v_pivot_215_, v_as_216_, v_i_217_, v_k_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_n_223_, lean_object* v_lo_224_, lean_object* v_hi_225_, lean_object* v_hhi_226_, lean_object* v_pivot_227_, lean_object* v_as_228_, lean_object* v_i_229_, lean_object* v_k_230_, lean_object* v_ilo_231_, lean_object* v_ik_232_, lean_object* v_w_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_358778973____hygCtx___hyg_2__spec__1_spec__1(v_n_223_, v_lo_224_, v_hi_225_, v_hhi_226_, v_pivot_227_, v_as_228_, v_i_229_, v_k_230_, v_ilo_231_, v_ik_232_, v_w_233_);
lean_dec(v_pivot_227_);
lean_dec(v_hi_225_);
lean_dec(v_lo_224_);
lean_dec(v_n_223_);
return v_res_234_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(lean_object* v___y_235_, lean_object* v_as_236_, lean_object* v_k_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_m_242_; lean_object* v_a_243_; uint8_t v___x_244_; 
v___x_240_ = lean_nat_add(v_x_238_, v_x_239_);
v___x_241_ = lean_unsigned_to_nat(1u);
v_m_242_ = lean_nat_shiftr(v___x_240_, v___x_241_);
lean_dec(v___x_240_);
v_a_243_ = lean_array_fget_borrowed(v_as_236_, v_m_242_);
v___x_244_ = l_Lean_Name_quickLt(v_a_243_, v_k_237_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
lean_dec(v_x_239_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Name_quickLt(v_k_237_, v_a_243_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
lean_dec(v_m_242_);
lean_dec(v_x_238_);
v___x_247_ = lean_nat_dec_le(v___x_245_, v___y_235_);
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = lean_nat_dec_eq(v_m_242_, v___x_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_nat_sub(v_m_242_, v___x_241_);
lean_dec(v_m_242_);
v___x_250_ = lean_nat_dec_lt(v___x_249_, v_x_238_);
if (v___x_250_ == 0)
{
v_x_239_ = v___x_249_;
goto _start;
}
else
{
lean_dec(v___x_249_);
lean_dec(v_x_238_);
return v___x_248_;
}
}
else
{
lean_dec(v_m_242_);
lean_dec(v_x_238_);
return v___x_244_;
}
}
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
lean_dec(v_x_238_);
v___x_252_ = lean_nat_add(v_m_242_, v___x_241_);
lean_dec(v_m_242_);
v___x_253_ = lean_nat_dec_le(v___x_252_, v_x_239_);
if (v___x_253_ == 0)
{
lean_dec(v___x_252_);
lean_dec(v_x_239_);
return v___x_253_;
}
else
{
v_x_238_ = v___x_252_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_235_ = stack[0].m_obj;
lean_object* v_as_236_ = stack[1].m_obj;
lean_object* v_k_237_ = stack[2].m_obj;
lean_object* v_x_238_ = stack[3].m_obj;
lean_object* v_x_239_ = stack[4].m_obj;
uint8_t v_res_255_;
v_res_255_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___y_235_, v_as_236_, v_k_237_, v_x_238_, v_x_239_);
stack->m_num = v_res_255_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object* v___y_256_, lean_object* v_as_257_, lean_object* v_k_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___y_256_, v_as_257_, v_k_258_, v_x_259_, v_x_260_);
lean_dec(v_k_258_);
lean_dec_ref(v_as_257_);
lean_dec(v___y_256_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
uint8_t l_Lean_isDeclMeta(lean_object* v_env_267_, lean_object* v_declName_268_){
_start:
{
lean_object* v___x_269_; uint8_t v_isModule_270_; 
v___x_269_ = l_Lean_Environment_header(v_env_267_);
v_isModule_270_ = lean_ctor_get_uint8(v___x_269_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_269_);
if (v_isModule_270_ == 0)
{
uint8_t v___x_271_; 
lean_dec_ref(v_env_267_);
v___x_271_ = 1;
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___y_274_; lean_object* v___x_281_; lean_object* v___y_283_; 
v___x_272_ = lean_box(1);
v___x_281_ = ((lean_object*)(l_Lean_isDeclMeta___closed__0));
if (lean_obj_tag(v_declName_268_) == 1)
{
lean_object* v_pre_296_; lean_object* v_str_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_pre_296_ = lean_ctor_get(v_declName_268_, 0);
v_str_297_ = lean_ctor_get(v_declName_268_, 1);
v___x_298_ = ((lean_object*)(l_Lean_isDeclMeta___closed__1));
v___x_299_ = lean_string_dec_eq(v_str_297_, v___x_298_);
if (v___x_299_ == 0)
{
v___y_283_ = v_declName_268_;
goto v___jp_282_;
}
else
{
v___y_283_ = v_pre_296_;
goto v___jp_282_;
}
}
else
{
v___y_283_ = v_declName_268_;
goto v___jp_282_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v_toEnvExtension_276_; lean_object* v_asyncMode_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_275_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_276_ = lean_ctor_get(v___x_275_, 0);
v_asyncMode_277_ = lean_ctor_get(v_toEnvExtension_276_, 2);
v___x_278_ = lean_box(0);
v___x_279_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_272_, v___x_275_, v_env_267_, v_asyncMode_277_, v___x_278_);
v___x_280_ = l_Lean_NameSet_contains(v___x_279_, v___y_274_);
lean_dec(v___x_279_);
return v___x_280_;
}
v___jp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_267_, v_declName_268_);
if (lean_obj_tag(v___x_284_) == 0)
{
v___y_274_ = v___y_283_;
goto v___jp_273_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v___x_287_ = 0;
v___x_288_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_281_, v___x_286_, v_env_267_, v_val_285_, v___x_287_);
lean_dec(v_val_285_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_array_get_size(v___x_288_);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v___x_288_);
v___y_274_ = v___y_283_;
goto v___jp_273_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v___x_290_, v___x_292_);
v___x_294_ = lean_nat_dec_le(v___x_289_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v___x_293_);
lean_dec_ref(v___x_288_);
v___y_274_ = v___y_283_;
goto v___jp_273_;
}
else
{
uint8_t v___x_295_; 
lean_inc(v___x_293_);
v___x_295_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_293_, v___x_288_, v___y_283_, v___x_289_, v___x_293_);
lean_dec_ref(v___x_288_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
v___y_274_ = v___y_283_;
goto v___jp_273_;
}
else
{
lean_dec_ref(v_env_267_);
return v_isModule_270_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_isDeclMeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_267_ = stack[0].m_obj;
lean_object* v_declName_268_ = stack[1].m_obj;
uint8_t v_res_300_;
v_res_300_ = l_Lean_isDeclMeta(v_env_267_, v_declName_268_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object* v_env_301_, lean_object* v_declName_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_isDeclMeta(v_env_301_, v_declName_302_);
lean_dec(v_declName_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(lean_object* v___y_305_, lean_object* v_as_306_, lean_object* v_k_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___y_305_, v_as_306_, v_k_307_, v_x_308_, v_x_309_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_305_ = stack[0].m_obj;
lean_object* v_as_306_ = stack[1].m_obj;
lean_object* v_k_307_ = stack[2].m_obj;
lean_object* v_x_308_ = stack[3].m_obj;
lean_object* v_x_309_ = stack[4].m_obj;
uint8_t v_res_312_;
v_res_312_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v___y_305_, v_as_306_, v_k_307_, v_x_308_, v_x_309_, lean_box(0));
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object* v___y_313_, lean_object* v_as_314_, lean_object* v_k_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v___y_313_, v_as_314_, v_k_315_, v_x_316_, v_x_317_, v_x_318_);
lean_dec(v_k_315_);
lean_dec_ref(v_as_314_);
lean_dec(v___y_313_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta___lam__0(lean_object* v___x_321_, lean_object* v_declName_322_, lean_object* v_s_323_){
_start:
{
lean_object* v_addEntryFn_324_; lean_object* v_importedEntries_325_; lean_object* v_state_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_addEntryFn_324_ = lean_ctor_get(v___x_321_, 3);
lean_inc(v_addEntryFn_324_);
lean_dec_ref(v___x_321_);
v_importedEntries_325_ = lean_ctor_get(v_s_323_, 0);
v_state_326_ = lean_ctor_get(v_s_323_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_s_323_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v_s_323_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_state_326_);
lean_inc(v_importedEntries_325_);
lean_dec(v_s_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_state_330_; lean_object* v___x_332_; 
v_state_330_ = lean_apply_2(v_addEntryFn_324_, v_state_326_, v_declName_322_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_state_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_importedEntries_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_state_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object* v_env_335_, lean_object* v_declName_336_){
_start:
{
uint8_t v___x_337_; 
lean_inc_ref(v_env_335_);
v___x_337_ = l_Lean_isDeclMeta(v_env_335_, v_declName_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v_toEnvExtension_339_; lean_object* v_asyncMode_340_; uint8_t v_logWrites_341_; lean_object* v___f_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_338_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_339_ = lean_ctor_get(v___x_338_, 0);
v_asyncMode_340_ = lean_ctor_get(v_toEnvExtension_339_, 2);
v_logWrites_341_ = lean_ctor_get_uint8(v_toEnvExtension_339_, sizeof(void*)*6);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_setDeclMeta___lam__0), 3, 2);
lean_closure_set(v___f_342_, 0, v___x_338_);
lean_closure_set(v___f_342_, 1, v_declName_336_);
v___x_343_ = lean_box(0);
v___x_344_ = 1;
if (v_logWrites_341_ == 0)
{
lean_object* v___x_345_; 
lean_inc_ref(v_toEnvExtension_339_);
v___x_345_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_339_, v_env_335_, v___f_342_, v_asyncMode_340_, v___x_343_, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_inc_ref_n(v_toEnvExtension_339_, 2);
v___x_346_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_339_, v_env_335_);
lean_dec_ref(v_env_335_);
v___x_347_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_339_, v___x_346_, v___f_342_, v_asyncMode_340_, v___x_343_, v___x_344_);
return v___x_347_;
}
}
else
{
lean_dec(v_declName_336_);
return v_env_335_;
}
}
}
uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object* v_msg_355_){
_start:
{
lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___f_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___f_356_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__0));
v___f_357_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__1));
v___f_358_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__2));
v___f_359_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__3));
v___f_360_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__4));
v___f_361_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__5));
v___f_362_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__6));
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___f_356_);
lean_ctor_set(v___x_363_, 1, v___f_357_);
v___x_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___f_358_);
lean_ctor_set(v___x_364_, 2, v___f_359_);
lean_ctor_set(v___x_364_, 3, v___f_360_);
lean_ctor_set(v___x_364_, 4, v___f_361_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___f_362_);
v___x_366_ = 0;
v___x_367_ = lean_box(v___x_366_);
v___x_368_ = l_instInhabitedOfMonad___redArg(v___x_365_, v___x_367_);
v___x_369_ = lean_panic_fn_borrowed(v___x_368_, v_msg_355_);
lean_dec(v___x_368_);
v___x_370_ = lean_unbox(v___x_369_);
lean_dec(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_getIRPhases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_355_ = stack[0].m_obj;
uint8_t v_res_371_;
v_res_371_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_355_);
stack->m_num = v_res_371_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object* v_msg_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_378_ = ((lean_object*)(l_Lean_getIRPhases___closed__2));
v___x_379_ = lean_unsigned_to_nat(14u);
v___x_380_ = lean_unsigned_to_nat(22u);
v___x_381_ = ((lean_object*)(l_Lean_getIRPhases___closed__1));
v___x_382_ = ((lean_object*)(l_Lean_getIRPhases___closed__0));
v___x_383_ = l_mkPanicMessageWithDecl(v___x_382_, v___x_381_, v___x_380_, v___x_379_, v___x_378_);
return v___x_383_;
}
}
uint8_t l_Lean_getIRPhases(lean_object* v_env_384_, lean_object* v_declName_385_){
_start:
{
lean_object* v___x_386_; uint8_t v_isModule_387_; 
v___x_386_ = l_Lean_Environment_header(v_env_384_);
v_isModule_387_ = lean_ctor_get_uint8(v___x_386_, sizeof(void*)*8 + 4);
if (v_isModule_387_ == 0)
{
uint8_t v___x_388_; 
lean_dec_ref(v___x_386_);
lean_dec(v_declName_385_);
lean_dec_ref(v_env_384_);
v___x_388_ = 2;
return v___x_388_;
}
else
{
lean_object* v_modules_389_; lean_object* v___x_390_; 
v_modules_389_ = lean_ctor_get(v___x_386_, 3);
lean_inc_ref(v_modules_389_);
lean_dec_ref(v___x_386_);
v___x_390_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_384_, v_declName_385_);
if (lean_obj_tag(v___x_390_) == 0)
{
uint8_t v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_modules_389_);
v___x_391_ = 0;
lean_inc(v_declName_385_);
lean_inc_ref(v_env_384_);
v___x_392_ = l_Lean_Environment_find_x3f(v_env_384_, v_declName_385_, v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
uint8_t v___x_393_; 
lean_dec(v_declName_385_);
lean_dec_ref(v_env_384_);
v___x_393_ = 2;
return v___x_393_;
}
else
{
lean_object* v_val_394_; uint8_t v___x_395_; 
v_val_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_392_, 1);
v___x_395_ = l_Lean_ConstantInfo_isCtor(v_val_394_);
lean_dec(v_val_394_);
if (v___x_395_ == 0)
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_isMarkedMeta(v_env_384_, v_declName_385_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 1;
return v___x_398_;
}
}
else
{
uint8_t v___x_399_; 
lean_dec(v_declName_385_);
lean_dec_ref(v_env_384_);
v___x_399_ = 2;
return v___x_399_;
}
}
}
else
{
lean_object* v_val_400_; uint8_t v___x_401_; 
v_val_400_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___x_390_, 1);
v___x_401_ = l_Lean_isMarkedMeta(v_env_384_, v_declName_385_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_array_get_size(v_modules_389_);
v___x_403_ = lean_nat_dec_lt(v_val_400_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
lean_dec(v_val_400_);
lean_dec_ref(v_modules_389_);
v___x_404_ = lean_obj_once(&l_Lean_getIRPhases___closed__3, &l_Lean_getIRPhases___closed__3_once, _init_l_Lean_getIRPhases___closed__3);
v___x_405_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_404_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; uint8_t v_irPhases_407_; 
v___x_406_ = lean_array_fget(v_modules_389_, v_val_400_);
lean_dec(v_val_400_);
lean_dec_ref(v_modules_389_);
v_irPhases_407_ = lean_ctor_get_uint8(v___x_406_, sizeof(void*)*1);
lean_dec(v___x_406_);
return v_irPhases_407_;
}
}
else
{
uint8_t v___x_408_; 
lean_dec(v_val_400_);
lean_dec_ref(v_modules_389_);
v___x_408_ = 1;
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getIRPhases_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_384_ = stack[0].m_obj;
lean_object* v_declName_385_ = stack[1].m_obj;
uint8_t v_res_409_;
v_res_409_ = l_Lean_getIRPhases(v_env_384_, v_declName_385_);
stack->m_num = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* v_env_410_, lean_object* v_declName_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_getIRPhases(v_env_410_, v_declName_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
