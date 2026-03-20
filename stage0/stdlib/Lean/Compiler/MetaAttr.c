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
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_notMetaExt;
LEAN_EXPORT lean_object* l_Lean_markMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markNotMeta___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markNotMeta(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__spec__0(lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
return v_x_35_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_39_; 
v_head_37_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_head_37_);
v_tail_38_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_tail_38_);
lean_dec_ref(v_x_36_);
v___x_39_ = l_Lean_NameSet_insert(v_x_35_, v_head_37_);
v_x_35_ = v___x_39_;
v_x_36_ = v_tail_38_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(lean_object* v_x_41_, lean_object* v_x_42_, lean_object* v_newEntries_43_, lean_object* v_s_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__spec__0(v_s_44_, v_newEntries_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_newEntries_48_, lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(v_x_46_, v_x_47_, v_newEntries_48_, v_s_49_);
lean_dec(v_x_47_);
lean_dec(v_x_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(lean_object* v___x_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object* v___x_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(v___x_54_);
return v_res_56_;
}
}
static lean_object* _init_l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_58_; lean_object* v___f_59_; 
v___x_58_ = l_Lean_NameSet_empty;
v___f_59_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_59_, 0, v___x_58_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___f_63_ = lean_obj_once(&l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_, &l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_);
v___x_64_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_));
v___x_65_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__12_00___x40_Lean_Compiler_MetaAttr_246726276____hygCtx___hyg_2_));
v___x_66_ = l_Lean_registerEnvExtension___redArg(v___f_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2____boxed(lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_markMeta(lean_object* v_env_69_, lean_object* v_declName_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v___x_72_ = l_Lean_TagDeclarationExtension_tag(v___x_71_, v_env_69_, v_declName_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNotMeta___lam__0(lean_object* v_declName_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_NameSet_insert(v_x_74_, v_declName_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_markNotMeta(lean_object* v_env_76_, lean_object* v_declName_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_Name_isAnonymous(v_declName_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v_asyncMode_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
v___x_79_ = l___private_Lean_Compiler_MetaAttr_0__Lean_notMetaExt;
v_asyncMode_80_ = lean_ctor_get(v___x_79_, 2);
lean_inc(v_asyncMode_80_);
lean_inc(v_declName_77_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_markNotMeta___lam__0), 2, 1);
lean_closure_set(v___f_81_, 0, v_declName_77_);
v___x_82_ = l_Lean_EnvExtension_modifyState___redArg(v___x_79_, v_env_76_, v___f_81_, v_asyncMode_80_, v_declName_77_);
lean_dec(v_asyncMode_80_);
return v___x_82_;
}
else
{
lean_dec(v_declName_77_);
return v_env_76_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_isMarkedMeta(lean_object* v_env_83_, lean_object* v_declName_84_){
_start:
{
lean_object* v___x_85_; lean_object* v_toEnvExtension_86_; lean_object* v_asyncMode_87_; uint8_t v___x_88_; 
v___x_85_ = l___private_Lean_Compiler_MetaAttr_0__Lean_metaExt;
v_toEnvExtension_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_toEnvExtension_86_);
v_asyncMode_87_ = lean_ctor_get(v_toEnvExtension_86_, 2);
lean_inc(v_asyncMode_87_);
lean_dec_ref(v_toEnvExtension_86_);
v___x_88_ = l_Lean_TagDeclarationExtension_isTagged(v___x_85_, v_env_83_, v_declName_84_, v_asyncMode_87_);
lean_dec(v_asyncMode_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_isMarkedMeta___boxed(lean_object* v_env_89_, lean_object* v_declName_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_isMarkedMeta(v_env_89_, v_declName_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_NameSet_empty;
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_es_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_array_mk(v_es_97_);
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v_x1_99_, lean_object* v_x2_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_Lean_NameSet_contains(v_x1_99_, v_x2_100_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 1;
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_x1_104_, lean_object* v_x2_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v_x1_104_, v_x2_105_);
lean_dec(v_x2_105_);
lean_dec(v_x1_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__0(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
return v_x_108_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_112_; 
v_head_110_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_head_110_);
v_tail_111_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_tail_111_);
lean_dec_ref(v_x_109_);
v___x_112_ = lean_array_push(v_x_108_, v_head_110_);
v_x_108_ = v___x_112_;
v_x_109_ = v_tail_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_115_, lean_object* v_lo_116_, lean_object* v_hi_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_lt(v_lo_116_, v_hi_117_);
if (v___x_118_ == 0)
{
lean_dec(v_lo_116_);
return v_as_115_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; uint8_t v___x_123_; 
v___x_119_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_116_);
v___x_120_ = l_Array_qpartition___redArg(v_as_115_, v___x_119_, v_lo_116_, v_hi_117_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_nat_dec_le(v_hi_117_, v_fst_121_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_snd_122_, v_lo_116_, v_fst_121_);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_fst_121_, v___x_125_);
lean_dec(v_fst_121_);
v_as_115_ = v___x_124_;
v_lo_116_ = v___x_126_;
goto _start;
}
else
{
lean_dec(v_fst_121_);
lean_dec(v_lo_116_);
return v_snd_122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_128_, lean_object* v_lo_129_, lean_object* v_hi_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_as_128_, v_lo_129_, v_hi_130_);
lean_dec(v_hi_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(lean_object* v___x_132_, lean_object* v_env_133_, lean_object* v_s_134_, lean_object* v_entries_135_, uint8_t v_x_136_){
_start:
{
if (v_x_136_ == 2)
{
lean_object* v___x_137_; lean_object* v_decls_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_132_);
v_decls_138_ = l_List_foldl___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__0(v___x_137_, v_entries_135_);
v___x_139_ = lean_array_get_size(v_decls_138_);
v___x_140_ = lean_nat_dec_eq(v___x_139_, v___x_132_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___y_144_; uint8_t v___x_148_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_sub(v___x_139_, v___x_141_);
v___x_148_ = lean_nat_dec_le(v___x_132_, v___x_142_);
if (v___x_148_ == 0)
{
lean_dec(v___x_132_);
lean_inc(v___x_142_);
v___y_144_ = v___x_142_;
goto v___jp_143_;
}
else
{
v___y_144_ = v___x_132_;
goto v___jp_143_;
}
v___jp_143_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___y_144_, v___x_142_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_dec(v___x_142_);
lean_inc(v___y_144_);
v___x_146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_decls_138_, v___y_144_, v___y_144_);
lean_dec(v___y_144_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_decls_138_, v___y_144_, v___x_142_);
lean_dec(v___x_142_);
return v___x_147_;
}
}
}
else
{
lean_dec(v___x_132_);
return v_decls_138_;
}
}
else
{
lean_object* v___x_149_; 
lean_dec(v_entries_135_);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_132_);
lean_dec(v___x_132_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v___x_150_, lean_object* v_env_151_, lean_object* v_s_152_, lean_object* v_entries_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_x_282__boxed_155_; lean_object* v_res_156_; 
v_x_282__boxed_155_ = lean_unbox(v_x_154_);
v_res_156_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___lam__3_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(v___x_150_, v_env_151_, v_s_152_, v_entries_153_, v_x_282__boxed_155_);
lean_dec(v_s_152_);
lean_dec_ref(v_env_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Compiler_MetaAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_));
v___x_184_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2_();
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1(lean_object* v_n_187_, lean_object* v_as_188_, lean_object* v_lo_189_, lean_object* v_hi_190_, lean_object* v_w_191_, lean_object* v_hlo_192_, lean_object* v_hhi_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___redArg(v_as_188_, v_lo_189_, v_hi_190_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_195_, lean_object* v_as_196_, lean_object* v_lo_197_, lean_object* v_hi_198_, lean_object* v_w_199_, lean_object* v_hlo_200_, lean_object* v_hhi_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_2418679097____hygCtx___hyg_2__spec__1(v_n_195_, v_as_196_, v_lo_197_, v_hi_198_, v_w_199_, v_hlo_200_, v_hhi_201_);
lean_dec(v_hi_198_);
lean_dec(v_n_195_);
return v_res_202_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(uint8_t v___x_203_, lean_object* v_as_204_, lean_object* v_k_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_m_210_; lean_object* v_a_211_; uint8_t v___x_212_; 
v___x_208_ = lean_nat_add(v_x_206_, v_x_207_);
v___x_209_ = lean_unsigned_to_nat(1u);
v_m_210_ = lean_nat_shiftr(v___x_208_, v___x_209_);
lean_dec(v___x_208_);
v_a_211_ = lean_array_fget_borrowed(v_as_204_, v_m_210_);
v___x_212_ = l_Lean_Name_quickLt(v_a_211_, v_k_205_);
if (v___x_212_ == 0)
{
uint8_t v___x_213_; 
lean_dec(v_x_207_);
v___x_213_ = l_Lean_Name_quickLt(v_k_205_, v_a_211_);
if (v___x_213_ == 0)
{
lean_dec(v_m_210_);
lean_dec(v_x_206_);
return v___x_203_;
}
else
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v_m_210_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_nat_sub(v_m_210_, v___x_209_);
lean_dec(v_m_210_);
v___x_217_ = lean_nat_dec_lt(v___x_216_, v_x_206_);
if (v___x_217_ == 0)
{
v_x_207_ = v___x_216_;
goto _start;
}
else
{
lean_dec(v___x_216_);
lean_dec(v_x_206_);
return v___x_212_;
}
}
else
{
lean_dec(v_m_210_);
lean_dec(v_x_206_);
return v___x_212_;
}
}
}
else
{
lean_object* v___x_219_; uint8_t v___x_220_; 
lean_dec(v_x_206_);
v___x_219_ = lean_nat_add(v_m_210_, v___x_209_);
lean_dec(v_m_210_);
v___x_220_ = lean_nat_dec_le(v___x_219_, v_x_207_);
if (v___x_220_ == 0)
{
lean_dec(v___x_219_);
lean_dec(v_x_207_);
return v___x_220_;
}
else
{
v_x_206_ = v___x_219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg___boxed(lean_object* v___x_222_, lean_object* v_as_223_, lean_object* v_k_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___x_434__boxed_227_; uint8_t v_res_228_; lean_object* v_r_229_; 
v___x_434__boxed_227_ = lean_unbox(v___x_222_);
v_res_228_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_434__boxed_227_, v_as_223_, v_k_224_, v_x_225_, v_x_226_);
lean_dec(v_k_224_);
lean_dec_ref(v_as_223_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l_Lean_isDeclMeta(lean_object* v_env_234_, lean_object* v_declName_235_){
_start:
{
lean_object* v___x_236_; uint8_t v_isModule_237_; 
v___x_236_ = l_Lean_Environment_header(v_env_234_);
v_isModule_237_ = lean_ctor_get_uint8(v___x_236_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_236_);
if (v_isModule_237_ == 0)
{
uint8_t v___x_238_; 
lean_dec_ref(v_env_234_);
v___x_238_ = 1;
return v___x_238_;
}
else
{
uint8_t v___x_239_; lean_object* v___y_241_; 
v___x_239_ = 0;
if (lean_obj_tag(v_declName_235_) == 1)
{
lean_object* v_pre_262_; lean_object* v_str_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_pre_262_ = lean_ctor_get(v_declName_235_, 0);
v_str_263_ = lean_ctor_get(v_declName_235_, 1);
v___x_264_ = ((lean_object*)(l_Lean_isDeclMeta___closed__1));
v___x_265_ = lean_string_dec_eq(v_str_263_, v___x_264_);
if (v___x_265_ == 0)
{
v___y_241_ = v_declName_235_;
goto v___jp_240_;
}
else
{
v___y_241_ = v_pre_262_;
goto v___jp_240_;
}
}
else
{
v___y_241_ = v_declName_235_;
goto v___jp_240_;
}
v___jp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_234_, v_declName_235_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v_toEnvExtension_244_; lean_object* v_asyncMode_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_243_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref(v_toEnvExtension_244_);
v_asyncMode_245_ = lean_ctor_get(v_toEnvExtension_244_, 2);
lean_inc(v_asyncMode_245_);
lean_dec_ref(v_toEnvExtension_244_);
v___x_246_ = lean_box(1);
v___x_247_ = lean_box(0);
v___x_248_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_246_, v___x_243_, v_env_234_, v_asyncMode_245_, v___x_247_);
lean_dec(v_asyncMode_245_);
v___x_249_ = l_Lean_NameSet_contains(v___x_248_, v___y_241_);
lean_dec(v___x_248_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_val_250_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_250_);
lean_dec_ref(v___x_242_);
v___x_251_ = ((lean_object*)(l_Lean_isDeclMeta___closed__0));
v___x_252_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v___x_253_ = 0;
v___x_254_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_251_, v___x_252_, v_env_234_, v_val_250_, v___x_253_);
lean_dec(v_val_250_);
lean_dec_ref(v_env_234_);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_array_get_size(v___x_254_);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v___x_254_);
return v___x_239_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_sub(v___x_256_, v___x_258_);
v___x_260_ = lean_nat_dec_le(v___x_255_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v___x_259_);
lean_dec_ref(v___x_254_);
return v___x_239_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v_isModule_237_, v___x_254_, v___y_241_, v___x_255_, v___x_259_);
lean_dec_ref(v___x_254_);
return v___x_261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDeclMeta___boxed(lean_object* v_env_266_, lean_object* v_declName_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_isDeclMeta(v_env_266_, v_declName_267_);
lean_dec(v_declName_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(uint8_t v___x_270_, lean_object* v_as_271_, lean_object* v_k_272_, lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___redArg(v___x_270_, v_as_271_, v_k_272_, v_x_273_, v_x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0___boxed(lean_object* v___x_277_, lean_object* v_as_278_, lean_object* v_k_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint8_t v___x_533__boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v___x_533__boxed_283_ = lean_unbox(v___x_277_);
v_res_284_ = l_Array_binSearchAux___at___00Lean_isDeclMeta_spec__0(v___x_533__boxed_283_, v_as_278_, v_k_279_, v_x_280_, v_x_281_, v_x_282_);
lean_dec(v_k_279_);
lean_dec_ref(v_as_278_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_setDeclMeta(lean_object* v_env_286_, lean_object* v_declName_287_){
_start:
{
uint8_t v___x_288_; 
lean_inc_ref(v_env_286_);
v___x_288_ = l_Lean_isDeclMeta(v_env_286_, v_declName_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v_toEnvExtension_290_; lean_object* v_asyncMode_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = l___private_Lean_Compiler_MetaAttr_0__Lean_declMetaExt;
v_toEnvExtension_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_toEnvExtension_290_);
v_asyncMode_291_ = lean_ctor_get(v_toEnvExtension_290_, 2);
lean_inc(v_asyncMode_291_);
lean_dec_ref(v_toEnvExtension_290_);
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_289_, v_env_286_, v_declName_287_, v_asyncMode_291_, v___x_292_);
lean_dec(v_asyncMode_291_);
return v___x_293_;
}
else
{
lean_dec(v_declName_287_);
return v_env_286_;
}
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_getIRPhases_spec__0(lean_object* v_msg_301_){
_start:
{
lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___f_302_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__0));
v___f_303_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__1));
v___f_304_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__2));
v___f_305_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__3));
v___f_306_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__4));
v___f_307_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__5));
v___f_308_ = ((lean_object*)(l_panic___at___00Lean_getIRPhases_spec__0___closed__6));
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___f_302_);
lean_ctor_set(v___x_309_, 1, v___f_303_);
v___x_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___f_304_);
lean_ctor_set(v___x_310_, 2, v___f_305_);
lean_ctor_set(v___x_310_, 3, v___f_306_);
lean_ctor_set(v___x_310_, 4, v___f_307_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___f_308_);
v___x_312_ = 0;
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = l_instInhabitedOfMonad___redArg(v___x_311_, v___x_313_);
v___x_315_ = lean_panic_fn(v___x_314_, v_msg_301_);
v___x_316_ = lean_unbox(v___x_315_);
lean_dec(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getIRPhases_spec__0___boxed(lean_object* v_msg_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_panic___at___00Lean_getIRPhases_spec__0(v_msg_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
static lean_object* _init_l_Lean_getIRPhases___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l_Lean_getIRPhases___closed__2));
v___x_324_ = lean_unsigned_to_nat(14u);
v___x_325_ = lean_unsigned_to_nat(22u);
v___x_326_ = ((lean_object*)(l_Lean_getIRPhases___closed__1));
v___x_327_ = ((lean_object*)(l_Lean_getIRPhases___closed__0));
v___x_328_ = l_mkPanicMessageWithDecl(v___x_327_, v___x_326_, v___x_325_, v___x_324_, v___x_323_);
return v___x_328_;
}
}
LEAN_EXPORT uint8_t l_Lean_getIRPhases(lean_object* v_env_329_, lean_object* v_declName_330_){
_start:
{
lean_object* v___x_331_; uint8_t v_isModule_332_; 
v___x_331_ = l_Lean_Environment_header(v_env_329_);
v_isModule_332_ = lean_ctor_get_uint8(v___x_331_, sizeof(void*)*7 + 4);
if (v_isModule_332_ == 0)
{
uint8_t v___x_333_; 
lean_dec_ref(v___x_331_);
lean_dec(v_declName_330_);
lean_dec_ref(v_env_329_);
v___x_333_ = 2;
return v___x_333_;
}
else
{
lean_object* v_modules_334_; lean_object* v___x_335_; 
v_modules_334_ = lean_ctor_get(v___x_331_, 3);
lean_inc_ref(v_modules_334_);
lean_dec_ref(v___x_331_);
v___x_335_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_329_, v_declName_330_);
if (lean_obj_tag(v___x_335_) == 0)
{
uint8_t v___x_336_; 
lean_dec_ref(v_modules_334_);
lean_inc(v_declName_330_);
lean_inc_ref(v_env_329_);
v___x_336_ = l_Lean_isMarkedMeta(v_env_329_, v_declName_330_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v_asyncMode_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_337_ = l___private_Lean_Compiler_MetaAttr_0__Lean_notMetaExt;
v_asyncMode_338_ = lean_ctor_get(v___x_337_, 2);
lean_inc(v_asyncMode_338_);
v___x_339_ = lean_box(1);
v___x_340_ = lean_box(0);
v___x_341_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_339_, v___x_337_, v_env_329_, v_asyncMode_338_, v___x_340_);
lean_dec(v_asyncMode_338_);
v___x_342_ = l_Lean_NameSet_contains(v___x_341_, v_declName_330_);
lean_dec(v_declName_330_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = 2;
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 0;
return v___x_344_;
}
}
else
{
uint8_t v___x_345_; 
lean_dec(v_declName_330_);
lean_dec_ref(v_env_329_);
v___x_345_ = 1;
return v___x_345_;
}
}
else
{
lean_object* v_val_346_; uint8_t v___x_347_; 
v_val_346_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_346_);
lean_dec_ref(v___x_335_);
v___x_347_ = l_Lean_isMarkedMeta(v_env_329_, v_declName_330_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_modules_334_);
v___x_349_ = lean_nat_dec_lt(v_val_346_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
lean_dec(v_val_346_);
lean_dec_ref(v_modules_334_);
v___x_350_ = lean_obj_once(&l_Lean_getIRPhases___closed__3, &l_Lean_getIRPhases___closed__3_once, _init_l_Lean_getIRPhases___closed__3);
v___x_351_ = l_panic___at___00Lean_getIRPhases_spec__0(v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; uint8_t v_irPhases_353_; 
v___x_352_ = lean_array_fget(v_modules_334_, v_val_346_);
lean_dec(v_val_346_);
lean_dec_ref(v_modules_334_);
v_irPhases_353_ = lean_ctor_get_uint8(v___x_352_, sizeof(void*)*1);
lean_dec(v___x_352_);
return v_irPhases_353_;
}
}
else
{
uint8_t v___x_354_; 
lean_dec(v_val_346_);
lean_dec_ref(v_modules_334_);
v___x_354_ = 1;
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getIRPhases___boxed(lean_object* v_env_355_, lean_object* v_declName_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Lean_getIRPhases(v_env_355_, v_declName_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
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
res = l___private_Lean_Compiler_MetaAttr_0__Lean_initFn_00___x40_Lean_Compiler_MetaAttr_285705796____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_MetaAttr_0__Lean_notMetaExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_MetaAttr_0__Lean_notMetaExt);
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
