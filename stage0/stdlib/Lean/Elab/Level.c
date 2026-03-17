// Lean compiler output
// Module: Lean.Elab.Level
// Imports: public import Lean.Elab.AutoBound
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
extern lean_object* l_Lean_Elab_relaxedAutoImplicit;
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_map, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_pure, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_seqRight, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_bind, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value),((lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value),((lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1 = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2 = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value),((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3 = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value),((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4 = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "maxUniverseOffset"};
static const lean_object* l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 24, 201, 205, 109, 178, 222, 7)}};
static const lean_object* l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "maximum universe level offset"};
static const lean_object* l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(223, 205, 225, 18, 63, 191, 162, 209)}};
static const lean_ctor_object l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 128, 181, 12, 212, 155, 25, 154)}};
static const lean_object* l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Universe level offset `"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` exceeds maximum offset `"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 209, .m_capacity = 209, .m_length = 208, .m_data = "This code is probably misusing universe levels, since they are usually small natural numbers. If you are confident this is not the case, you can increase the limit using `set_option maxUniverseOffset <limit>`"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ill-formed syntax"};
static const lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__1 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__1_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__0 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__2 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__3 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__4 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__5 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__6 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__7 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__7_value),LEAN_SCALAR_PTR_LITERAL(144, 86, 172, 30, 114, 81, 66, 18)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__8 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__9 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__9_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__10 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__10_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__11 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__12 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__12_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "addLit"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__13 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__13_value),LEAN_SCALAR_PTR_LITERAL(53, 243, 225, 2, 30, 243, 80, 174)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__14 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "unexpected universe level syntax kind"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__15 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Level_elabLevel___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__16;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unknown universe level `"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__17 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Level_elabLevel___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__18;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v_options_4_; lean_object* v___x_5_; 
v_options_4_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc_ref(v_options_4_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_options_4_);
lean_ctor_set(v___x_5_, 1, v___y_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object* v_____do__lift_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(v_____do__lift_6_, v___y_7_, v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec_ref(v_____do__lift_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object* v_____do__lift_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_40_; lean_object* v___x_41_; 
v_ref_40_ = lean_ctor_get(v_____do__lift_37_, 1);
lean_inc(v_ref_40_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v_ref_40_);
lean_ctor_set(v___x_41_, 1, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object* v_____do__lift_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(v_____do__lift_42_, v___y_43_, v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec_ref(v_____do__lift_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object* v_00_u03b1_46_, lean_object* v_ref_47_, lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_options_51_; uint8_t v_autoBoundImplicit_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
v_options_51_ = lean_ctor_get(v___y_49_, 0);
v_autoBoundImplicit_52_ = lean_ctor_get_uint8(v___y_49_, sizeof(void*)*2);
v_isSharedCheck_60_ = !lean_is_exclusive(v___y_49_);
if (v_isSharedCheck_60_ == 0)
{
lean_object* v_unused_61_; 
v_unused_61_ = lean_ctor_get(v___y_49_, 1);
lean_dec(v_unused_61_);
v___x_54_ = v___y_49_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_options_51_);
lean_dec(v___y_49_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v_ref_47_);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_options_51_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_ref_47_);
lean_ctor_set_uint8(v_reuseFailAlloc_59_, sizeof(void*)*2, v_autoBoundImplicit_52_);
v___x_57_ = v_reuseFailAlloc_59_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_2(v_x_48_, v___x_57_, v___y_50_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object* v_msg_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_msg_72_);
lean_ctor_set(v___x_75_, 1, v___y_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(v_msg_76_, v___y_77_, v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_84_; 
lean_inc_ref(v___y_83_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_83_);
lean_ctor_set(v___x_84_, 1, v___y_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(v___y_85_, v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object* v_____do__lift_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_ngen_91_; lean_object* v___x_92_; 
v_ngen_91_ = lean_ctor_get(v_____do__lift_88_, 0);
lean_inc_ref(v_ngen_91_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_ngen_91_);
lean_ctor_set(v___x_92_, 1, v___y_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object* v_____do__lift_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(v_____do__lift_93_, v___y_94_, v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec_ref(v_____do__lift_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object* v_ngen_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_mctx_100_; lean_object* v_levelNames_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
v_mctx_100_ = lean_ctor_get(v___y_99_, 1);
v_levelNames_101_ = lean_ctor_get(v___y_99_, 2);
v_isSharedCheck_110_ = !lean_is_exclusive(v___y_99_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v___y_99_, 0);
lean_dec(v_unused_111_);
v___x_103_ = v___y_99_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_levelNames_101_);
lean_inc(v_mctx_100_);
lean_dec(v___y_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_box(0);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v_ngen_97_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_mctx_100_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_levelNames_101_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_105_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object* v_ngen_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(v_ngen_112_, v___y_113_, v___y_114_);
lean_dec_ref(v___y_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object* v___y_127_){
_start:
{
lean_object* v_ngen_128_; lean_object* v_mctx_129_; lean_object* v_levelNames_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_150_; 
v_ngen_128_ = lean_ctor_get(v___y_127_, 0);
v_mctx_129_ = lean_ctor_get(v___y_127_, 1);
v_levelNames_130_ = lean_ctor_get(v___y_127_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v___y_127_);
if (v_isSharedCheck_150_ == 0)
{
v___x_132_ = v___y_127_;
v_isShared_133_ = v_isSharedCheck_150_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_levelNames_130_);
lean_inc(v_mctx_129_);
lean_inc(v_ngen_128_);
lean_dec(v___y_127_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_150_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_namePrefix_134_; lean_object* v_idx_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_149_; 
v_namePrefix_134_ = lean_ctor_get(v_ngen_128_, 0);
v_idx_135_ = lean_ctor_get(v_ngen_128_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_ngen_128_);
if (v_isSharedCheck_149_ == 0)
{
v___x_137_ = v_ngen_128_;
v_isShared_138_ = v_isSharedCheck_149_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_idx_135_);
lean_inc(v_namePrefix_134_);
lean_dec(v_ngen_128_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_149_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_r_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
lean_inc(v_idx_135_);
lean_inc(v_namePrefix_134_);
v_r_139_ = l_Lean_Name_num___override(v_namePrefix_134_, v_idx_135_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_idx_135_, v___x_140_);
lean_dec(v_idx_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_141_);
v___x_143_ = v___x_137_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_namePrefix_134_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_143_);
v___x_145_ = v___x_132_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_mctx_129_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_levelNames_130_);
v___x_145_ = v_reuseFailAlloc_147_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_r_139_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v___x_153_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_152_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_a_155_ = lean_ctor_get(v___x_153_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_153_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v___y_163_, v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_189_; 
v_a_169_ = lean_ctor_get(v___x_168_, 1);
v_a_170_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_189_ == 0)
{
v___x_172_ = v___x_168_;
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_169_);
lean_inc(v_a_170_);
lean_dec(v___x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_ngen_174_; lean_object* v_mctx_175_; lean_object* v_levelNames_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_188_; 
v_ngen_174_ = lean_ctor_get(v_a_169_, 0);
v_mctx_175_ = lean_ctor_get(v_a_169_, 1);
v_levelNames_176_ = lean_ctor_get(v_a_169_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_a_169_);
if (v_isSharedCheck_188_ == 0)
{
v___x_178_ = v_a_169_;
v_isShared_179_ = v_isSharedCheck_188_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_levelNames_176_);
lean_inc(v_mctx_175_);
lean_inc(v_ngen_174_);
lean_dec(v_a_169_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_188_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
lean_inc(v_a_170_);
v___x_180_ = l_Lean_MetavarContext_addLevelMVarDecl(v_mctx_175_, v_a_170_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_ngen_174_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_levelNames_176_);
v___x_182_ = v_reuseFailAlloc_187_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = l_Lean_mkLevelMVar(v_a_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_182_);
lean_ctor_set(v___x_172_, 0, v___x_183_);
v___x_185_ = v___x_172_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_182_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_a_190_ = lean_ctor_get(v___x_168_, 0);
v_a_191_ = lean_ctor_get(v___x_168_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_168_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_inc(v_a_190_);
lean_dec(v___x_168_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_190_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Elab_Level_mkFreshLevelMVar(v_a_199_, v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(v___y_205_, v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* v_name_208_, lean_object* v_decl_209_, lean_object* v_ref_210_){
_start:
{
lean_object* v_defValue_212_; lean_object* v_descr_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_239_; 
v_defValue_212_ = lean_ctor_get(v_decl_209_, 0);
v_descr_213_ = lean_ctor_get(v_decl_209_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_decl_209_);
if (v_isSharedCheck_239_ == 0)
{
v___x_215_ = v_decl_209_;
v_isShared_216_ = v_isSharedCheck_239_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_descr_213_);
lean_inc(v_defValue_212_);
lean_dec(v_decl_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_239_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc(v_defValue_212_);
v___x_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_217_, 0, v_defValue_212_);
lean_inc(v_name_208_);
v___x_218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_218_, 0, v_name_208_);
lean_ctor_set(v___x_218_, 1, v_ref_210_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
lean_ctor_set(v___x_218_, 3, v_descr_213_);
lean_inc(v_name_208_);
v___x_219_ = lean_register_option(v_name_208_, v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_219_, 0);
lean_dec(v_unused_230_);
v___x_221_ = v___x_219_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_dec(v___x_219_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v_defValue_212_);
lean_ctor_set(v___x_215_, 0, v_name_208_);
v___x_224_ = v___x_215_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_name_208_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_defValue_212_);
v___x_224_ = v_reuseFailAlloc_228_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_226_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_del_object(v___x_215_);
lean_dec(v_defValue_212_);
lean_dec(v_name_208_);
v_a_231_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_219_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_219_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_240_, lean_object* v_decl_241_, lean_object* v_ref_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_240_, v_decl_241_, v_ref_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_262_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_263_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_264_ = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v___x_261_, v___x_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
return v_res_266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7);
v___x_280_ = l_Lean_MessageData_note(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object* v___x_281_, lean_object* v_n_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_toApplicative_285_, lean_object* v_____do__lift_286_){
_start:
{
lean_object* v___x_287_; lean_object* v_max_288_; uint8_t v___x_289_; 
v___x_287_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_288_ = l_Lean_Option_get___redArg(v___x_281_, v_____do__lift_286_, v___x_287_);
v___x_289_ = lean_nat_dec_le(v_n_282_, v_max_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_toApplicative_285_);
v___x_290_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_291_ = l_Nat_reprFast(v_n_282_);
v___x_292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = l_Lean_MessageData_ofFormat(v___x_292_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_290_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Nat_reprFast(v_max_288_);
v___x_298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
v___x_299_ = l_Lean_MessageData_ofFormat(v___x_298_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_296_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_throwError___redArg(v_inst_283_, v_inst_284_, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v_toPure_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_max_288_);
lean_dec_ref(v_inst_284_);
lean_dec_ref(v_inst_283_);
lean_dec(v_n_282_);
v_toPure_306_ = lean_ctor_get(v_toApplicative_285_, 1);
lean_inc(v_toPure_306_);
lean_dec_ref(v_toApplicative_285_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_2(v_toPure_306_, lean_box(0), v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* v___x_309_, lean_object* v_n_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_toApplicative_313_, lean_object* v_____do__lift_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(v___x_309_, v_n_310_, v_inst_311_, v_inst_312_, v_toApplicative_313_, v_____do__lift_314_);
lean_dec_ref(v_____do__lift_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_n_319_){
_start:
{
lean_object* v___x_320_; lean_object* v_toApplicative_321_; lean_object* v_toBind_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
v___x_320_ = l_Lean_KVMap_instValueNat;
v_toApplicative_321_ = lean_ctor_get(v_inst_316_, 0);
lean_inc_ref(v_toApplicative_321_);
v_toBind_322_ = lean_ctor_get(v_inst_316_, 1);
lean_inc(v_toBind_322_);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_323_, 0, v___x_320_);
lean_closure_set(v___f_323_, 1, v_n_319_);
lean_closure_set(v___f_323_, 2, v_inst_316_);
lean_closure_set(v___f_323_, 3, v_inst_317_);
lean_closure_set(v___f_323_, 4, v_toApplicative_321_);
v___x_324_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_inst_318_, v___f_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* v_m_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_n_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(v_inst_326_, v_inst_327_, v_inst_328_, v_n_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_ref_334_ = lean_ctor_get(v___y_332_, 1);
lean_inc(v_ref_334_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_ref_334_);
lean_ctor_set(v___x_335_, 1, v_msg_331_);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___y_333_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_337_, v___y_338_, v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object* v_00_u03b1_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_342_, v___y_343_, v___y_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* v_00_u03b1_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(v_00_u03b1_346_, v_msg_347_, v___y_348_, v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object* v_opts_351_, lean_object* v_opt_352_){
_start:
{
lean_object* v_name_353_; lean_object* v_defValue_354_; lean_object* v_map_355_; lean_object* v___x_356_; 
v_name_353_ = lean_ctor_get(v_opt_352_, 0);
v_defValue_354_ = lean_ctor_get(v_opt_352_, 1);
v_map_355_ = lean_ctor_get(v_opts_351_, 0);
v___x_356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_355_, v_name_353_);
if (lean_obj_tag(v___x_356_) == 0)
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_defValue_354_);
return v___x_357_;
}
else
{
lean_object* v_val_358_; 
v_val_358_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_358_);
lean_dec_ref(v___x_356_);
if (lean_obj_tag(v_val_358_) == 1)
{
uint8_t v_v_359_; 
v_v_359_ = lean_ctor_get_uint8(v_val_358_, 0);
lean_dec_ref(v_val_358_);
return v_v_359_;
}
else
{
uint8_t v___x_360_; 
lean_dec(v_val_358_);
v___x_360_ = lean_unbox(v_defValue_354_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* v_opts_361_, lean_object* v_opt_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_361_, v_opt_362_);
lean_dec_ref(v_opt_362_);
lean_dec_ref(v_opts_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
v___x_371_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_370_, v___y_368_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_372_, v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_374_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(lean_object* v_a_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
uint8_t v___x_377_; 
v___x_377_ = 0;
return v___x_377_;
}
else
{
lean_object* v_head_378_; lean_object* v_tail_379_; uint8_t v___x_380_; 
v_head_378_ = lean_ctor_get(v_x_376_, 0);
v_tail_379_ = lean_ctor_get(v_x_376_, 1);
v___x_380_ = lean_name_eq(v_a_375_, v_head_378_);
if (v___x_380_ == 0)
{
v_x_376_ = v_tail_379_;
goto _start;
}
else
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object* v_a_382_, lean_object* v_x_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_382_, v_x_383_);
lean_dec(v_x_383_);
lean_dec(v_a_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* v_opts_386_, lean_object* v_opt_387_){
_start:
{
lean_object* v_name_388_; lean_object* v_defValue_389_; lean_object* v_map_390_; lean_object* v___x_391_; 
v_name_388_ = lean_ctor_get(v_opt_387_, 0);
v_defValue_389_ = lean_ctor_get(v_opt_387_, 1);
v_map_390_ = lean_ctor_get(v_opts_386_, 0);
v___x_391_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_390_, v_name_388_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_inc(v_defValue_389_);
return v_defValue_389_;
}
else
{
lean_object* v_val_392_; 
v_val_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_392_);
lean_dec_ref(v___x_391_);
if (lean_obj_tag(v_val_392_) == 3)
{
lean_object* v_v_393_; 
v_v_393_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_v_393_);
lean_dec_ref(v_val_392_);
return v_v_393_;
}
else
{
lean_dec(v_val_392_);
lean_inc(v_defValue_389_);
return v_defValue_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* v_opts_394_, lean_object* v_opt_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_opts_394_, v_opt_395_);
lean_dec_ref(v_opt_395_);
lean_dec_ref(v_opts_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object* v_n_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_options_400_; lean_object* v___x_401_; lean_object* v_max_402_; uint8_t v___x_403_; 
v_options_400_ = lean_ctor_get(v___y_398_, 0);
v___x_401_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_402_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_options_400_, v___x_401_);
v___x_403_ = lean_nat_dec_le(v_n_397_, v_max_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_404_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_405_ = l_Nat_reprFast(v_n_397_);
v___x_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
v___x_407_ = l_Lean_MessageData_ofFormat(v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Nat_reprFast(v_max_402_);
v___x_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
v___x_413_ = l_Lean_MessageData_ofFormat(v___x_412_);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_410_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_418_, v___y_398_, v___y_399_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_max_402_);
lean_dec(v_n_397_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___y_399_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* v_n_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_n_422_, v___y_423_, v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__15));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__17));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object* v_as_469_, size_t v_i_470_, size_t v_stop_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_eq(v_i_470_, v_stop_471_);
if (v___x_475_ == 0)
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_sub(v_i_470_, v___x_476_);
v___x_478_ = lean_array_uget_borrowed(v_as_469_, v___x_477_);
lean_inc_ref(v___y_473_);
lean_inc(v___x_478_);
v___x_479_ = l_Lean_Elab_Level_elabLevel(v___x_478_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
v_a_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_a_481_);
lean_dec_ref(v___x_479_);
v___x_482_ = l_Lean_mkLevelMax_x27(v_a_480_, v_b_472_);
v_i_470_ = v___x_477_;
v_b_472_ = v___x_482_;
v___y_474_ = v_a_481_;
goto _start;
}
else
{
lean_dec(v_b_472_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_484_; lean_object* v_a_485_; 
v_a_484_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_484_);
v_a_485_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_a_485_);
lean_dec_ref(v___x_479_);
v_i_470_ = v___x_477_;
v_b_472_ = v_a_484_;
v___y_474_ = v_a_485_;
goto _start;
}
else
{
lean_dec_ref(v___y_473_);
return v___x_479_;
}
}
}
else
{
lean_object* v___x_487_; 
lean_dec_ref(v___y_473_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_b_472_);
lean_ctor_set(v___x_487_, 1, v___y_474_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* v_stx_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_options_491_; lean_object* v_ref_492_; uint8_t v_autoBoundImplicit_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_666_; 
v_options_491_ = lean_ctor_get(v_a_489_, 0);
v_ref_492_ = lean_ctor_get(v_a_489_, 1);
v_autoBoundImplicit_493_ = lean_ctor_get_uint8(v_a_489_, sizeof(void*)*2);
v_isSharedCheck_666_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_666_ == 0)
{
v___x_495_ = v_a_489_;
v_isShared_496_ = v_isSharedCheck_666_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_ref_492_);
lean_inc(v_options_491_);
lean_dec(v_a_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_666_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_kind_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v_ref_500_; lean_object* v___x_502_; 
lean_inc(v_stx_488_);
v_kind_497_ = l_Lean_Syntax_getKind(v_stx_488_);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__2));
v___x_499_ = lean_name_eq(v_kind_497_, v___x_498_);
v_ref_500_ = l_Lean_replaceRef(v_stx_488_, v_ref_492_);
lean_dec(v_ref_492_);
lean_inc_ref(v_options_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v_ref_500_);
v___x_502_ = v___x_495_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_options_491_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_ref_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_665_, sizeof(void*)*2, v_autoBoundImplicit_493_);
v___x_502_ = v_reuseFailAlloc_665_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
if (v___x_499_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__4));
v___x_504_ = lean_name_eq(v_kind_497_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__6));
v___x_506_ = lean_name_eq(v_kind_497_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__8));
v___x_508_ = lean_name_eq(v_kind_497_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__10));
v___x_510_ = lean_name_eq(v_kind_497_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__12));
v___x_512_ = lean_name_eq(v_kind_497_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
lean_dec_ref(v_options_491_);
v___x_513_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__14));
v___x_514_ = lean_name_eq(v_kind_497_, v___x_513_);
lean_dec(v_kind_497_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_stx_488_);
v___x_515_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__16, &l_Lean_Elab_Level_elabLevel___closed__16_once, _init_l_Lean_Elab_Level_elabLevel___closed__16);
v___x_516_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_515_, v___x_502_, v_a_490_);
lean_dec_ref(v___x_502_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_Syntax_getArg(v_stx_488_, v___x_517_);
lean_inc_ref(v___x_502_);
v___x_519_ = l_Lean_Elab_Level_elabLevel(v___x_518_, v___x_502_, v_a_490_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v_a_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_a_521_);
lean_dec_ref(v___x_519_);
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = l_Lean_Syntax_getArg(v_stx_488_, v___x_522_);
lean_dec(v_stx_488_);
v___x_524_ = l_Lean_Syntax_isNatLit_x3f(v___x_523_);
lean_dec(v___x_523_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_525_; 
lean_dec(v_a_520_);
v___x_525_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_502_, v_a_521_);
lean_dec_ref(v___x_502_);
return v___x_525_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
v_val_526_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_val_526_);
lean_dec_ref(v___x_524_);
lean_inc(v_val_526_);
v___x_527_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_526_, v___x_502_, v_a_521_);
lean_dec_ref(v___x_502_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v___x_527_, 0);
lean_dec(v_unused_537_);
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_Level_addOffset(v_a_520_, v_val_526_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_val_526_);
lean_dec(v_a_520_);
v_a_538_ = lean_ctor_get(v___x_527_, 0);
v_a_539_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_527_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_inc(v_a_538_);
lean_dec(v___x_527_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_538_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_502_);
lean_dec(v_stx_488_);
return v___x_519_;
}
}
}
else
{
lean_object* v_ngen_547_; lean_object* v_mctx_548_; lean_object* v_levelNames_549_; lean_object* v_paramName_550_; lean_object* v___y_552_; uint8_t v___x_573_; 
lean_dec(v_kind_497_);
v_ngen_547_ = lean_ctor_get(v_a_490_, 0);
v_mctx_548_ = lean_ctor_get(v_a_490_, 1);
v_levelNames_549_ = lean_ctor_get(v_a_490_, 2);
v_paramName_550_ = l_Lean_Syntax_getId(v_stx_488_);
lean_dec(v_stx_488_);
v___x_573_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_paramName_550_, v_levelNames_549_);
if (v___x_573_ == 0)
{
if (v_autoBoundImplicit_493_ == 0)
{
lean_dec_ref(v_options_491_);
goto v___jp_555_;
}
else
{
lean_object* v___x_574_; uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_574_ = l_Lean_Elab_relaxedAutoImplicit;
v___x_575_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_491_, v___x_574_);
lean_dec_ref(v_options_491_);
lean_inc(v_paramName_550_);
v___x_576_ = l_Lean_Elab_isValidAutoBoundLevelName(v_paramName_550_, v___x_575_);
if (v___x_576_ == 0)
{
goto v___jp_555_;
}
else
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_584_; 
lean_inc(v_levelNames_549_);
lean_inc_ref(v_mctx_548_);
lean_inc_ref(v_ngen_547_);
lean_dec_ref(v___x_502_);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_585_ = lean_ctor_get(v_a_490_, 2);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_a_490_, 1);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_a_490_, 0);
lean_dec(v_unused_587_);
v___x_578_ = v_a_490_;
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
else
{
lean_dec(v_a_490_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_inc(v_paramName_550_);
v___x_580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_580_, 0, v_paramName_550_);
lean_ctor_set(v___x_580_, 1, v_levelNames_549_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 2, v___x_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_mctx_548_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_552_ = v___x_582_;
goto v___jp_551_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_502_);
lean_dec_ref(v_options_491_);
v___y_552_ = v_a_490_;
goto v___jp_551_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l_Lean_mkLevelParam(v_paramName_550_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___y_552_);
return v___x_554_;
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_556_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__18, &l_Lean_Elab_Level_elabLevel___closed__18_once, _init_l_Lean_Elab_Level_elabLevel___closed__18);
lean_inc(v_paramName_550_);
v___x_557_ = lean_mk_syntax_ident(v_paramName_550_);
v___x_558_ = l_Lean_MessageData_ofSyntax(v___x_557_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_556_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_561_, v___x_502_, v_a_490_);
lean_dec_ref(v___x_502_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; 
v_a_563_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_a_563_);
lean_dec_ref(v___x_562_);
v___y_552_ = v_a_563_;
goto v___jp_551_;
}
else
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_paramName_550_);
v_a_564_ = lean_ctor_get(v___x_562_, 0);
v_a_565_ = lean_ctor_get(v___x_562_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_562_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_inc(v_a_564_);
lean_dec(v___x_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_564_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_491_);
v___x_588_ = l_Lean_Syntax_isNatLit_x3f(v_stx_488_);
lean_dec(v_stx_488_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_502_, v_a_490_);
lean_dec_ref(v___x_502_);
return v___x_589_;
}
else
{
lean_object* v_val_590_; lean_object* v___x_591_; 
v_val_590_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v___x_588_);
lean_inc(v_val_590_);
v___x_591_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_590_, v___x_502_, v_a_490_);
lean_dec_ref(v___x_502_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_592_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_601_);
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Level_ofNat(v_val_590_);
lean_dec(v_val_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_a_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_val_590_);
v_a_602_ = lean_ctor_get(v___x_591_, 0);
v_a_603_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_591_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_inc(v_a_602_);
lean_dec(v___x_591_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
else
{
lean_object* v___x_611_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_491_);
lean_dec(v_stx_488_);
v___x_611_ = l_Lean_Elab_Level_mkFreshLevelMVar(v___x_502_, v_a_490_);
lean_dec_ref(v___x_502_);
return v___x_611_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_args_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_491_);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = l_Lean_Syntax_getArg(v_stx_488_, v___x_612_);
lean_dec(v_stx_488_);
v_args_614_ = l_Lean_Syntax_getArgs(v___x_613_);
lean_dec(v___x_613_);
v___x_615_ = lean_box(0);
v___x_616_ = lean_array_get_size(v_args_614_);
v___x_617_ = lean_nat_sub(v___x_616_, v___x_612_);
v___x_618_ = lean_array_get(v___x_615_, v_args_614_, v___x_617_);
lean_inc_ref(v___x_502_);
v___x_619_ = l_Lean_Elab_Level_elabLevel(v___x_618_, v___x_502_, v_a_490_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_array_624_; lean_object* v_start_625_; lean_object* v_stop_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
lean_inc(v_a_621_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Array_toSubarray___redArg(v_args_614_, v___x_622_, v___x_617_);
v_array_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_array_624_);
v_start_625_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_start_625_);
v_stop_626_ = lean_ctor_get(v___x_623_, 2);
lean_inc(v_stop_626_);
lean_dec_ref(v___x_623_);
v___x_627_ = lean_array_get_size(v_array_624_);
v___x_628_ = lean_nat_dec_le(v_stop_626_, v___x_627_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
lean_dec(v_stop_626_);
v___x_629_ = lean_nat_dec_lt(v_start_625_, v___x_627_);
if (v___x_629_ == 0)
{
lean_dec(v_start_625_);
lean_dec_ref(v_array_624_);
lean_dec(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v___x_502_);
return v___x_619_;
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v___x_619_);
v___x_630_ = lean_usize_of_nat(v___x_627_);
v___x_631_ = lean_usize_of_nat(v_start_625_);
lean_dec(v_start_625_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_624_, v___x_630_, v___x_631_, v_a_620_, v___x_502_, v_a_621_);
lean_dec_ref(v_array_624_);
return v___x_632_;
}
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_lt(v_start_625_, v_stop_626_);
if (v___x_633_ == 0)
{
lean_dec(v_stop_626_);
lean_dec(v_start_625_);
lean_dec_ref(v_array_624_);
lean_dec(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v___x_502_);
return v___x_619_;
}
else
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v___x_619_);
v___x_634_ = lean_usize_of_nat(v_stop_626_);
lean_dec(v_stop_626_);
v___x_635_ = lean_usize_of_nat(v_start_625_);
lean_dec(v_start_625_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_624_, v___x_634_, v___x_635_, v_a_620_, v___x_502_, v_a_621_);
lean_dec_ref(v_array_624_);
return v___x_636_;
}
}
}
else
{
lean_dec(v___x_617_);
lean_dec_ref(v_args_614_);
lean_dec_ref(v___x_502_);
return v___x_619_;
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_args_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_491_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = l_Lean_Syntax_getArg(v_stx_488_, v___x_637_);
lean_dec(v_stx_488_);
v_args_639_ = l_Lean_Syntax_getArgs(v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_array_get_size(v_args_639_);
v___x_642_ = lean_nat_sub(v___x_641_, v___x_637_);
v___x_643_ = lean_array_get(v___x_640_, v_args_639_, v___x_642_);
lean_inc_ref(v___x_502_);
v___x_644_ = l_Lean_Elab_Level_elabLevel(v___x_643_, v___x_502_, v_a_490_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_array_649_; lean_object* v_start_650_; lean_object* v_stop_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_646_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_Array_toSubarray___redArg(v_args_639_, v___x_647_, v___x_642_);
v_array_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_array_649_);
v_start_650_ = lean_ctor_get(v___x_648_, 1);
lean_inc(v_start_650_);
v_stop_651_ = lean_ctor_get(v___x_648_, 2);
lean_inc(v_stop_651_);
lean_dec_ref(v___x_648_);
v___x_652_ = lean_array_get_size(v_array_649_);
v___x_653_ = lean_nat_dec_le(v_stop_651_, v___x_652_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
lean_dec(v_stop_651_);
v___x_654_ = lean_nat_dec_lt(v_start_650_, v___x_652_);
if (v___x_654_ == 0)
{
lean_dec(v_start_650_);
lean_dec_ref(v_array_649_);
lean_dec(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v___x_502_);
return v___x_644_;
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v___x_644_);
v___x_655_ = lean_usize_of_nat(v___x_652_);
v___x_656_ = lean_usize_of_nat(v_start_650_);
lean_dec(v_start_650_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_649_, v___x_655_, v___x_656_, v_a_645_, v___x_502_, v_a_646_);
lean_dec_ref(v_array_649_);
return v___x_657_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_lt(v_start_650_, v_stop_651_);
if (v___x_658_ == 0)
{
lean_dec(v_stop_651_);
lean_dec(v_start_650_);
lean_dec_ref(v_array_649_);
lean_dec(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v___x_502_);
return v___x_644_;
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v___x_644_);
v___x_659_ = lean_usize_of_nat(v_stop_651_);
lean_dec(v_stop_651_);
v___x_660_ = lean_usize_of_nat(v_start_650_);
lean_dec(v_start_650_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_649_, v___x_659_, v___x_660_, v_a_645_, v___x_502_, v_a_646_);
lean_dec_ref(v_array_649_);
return v___x_661_;
}
}
}
else
{
lean_dec(v___x_642_);
lean_dec_ref(v_args_639_);
lean_dec_ref(v___x_502_);
return v___x_644_;
}
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_491_);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = l_Lean_Syntax_getArg(v_stx_488_, v___x_662_);
lean_dec(v_stx_488_);
v_stx_488_ = v___x_663_;
v_a_489_ = v___x_502_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* v_as_667_, size_t v_i_668_, size_t v_stop_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_eq(v_i_668_, v_stop_669_);
if (v___x_673_ == 0)
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_sub(v_i_668_, v___x_674_);
v___x_676_ = lean_array_uget_borrowed(v_as_667_, v___x_675_);
lean_inc_ref(v___y_671_);
lean_inc(v___x_676_);
v___x_677_ = l_Lean_Elab_Level_elabLevel(v___x_676_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
v_a_679_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_a_679_);
lean_dec_ref(v___x_677_);
v___x_680_ = l_Lean_mkLevelIMax_x27(v_a_678_, v_b_670_);
v_i_668_ = v___x_675_;
v_b_670_ = v___x_680_;
v___y_672_ = v_a_679_;
goto _start;
}
else
{
lean_dec(v_b_670_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_682_; lean_object* v_a_683_; 
v_a_682_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_682_);
v_a_683_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_a_683_);
lean_dec_ref(v___x_677_);
v_i_668_ = v___x_675_;
v_b_670_ = v_a_682_;
v___y_672_ = v_a_683_;
goto _start;
}
else
{
lean_dec_ref(v___y_671_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_685_; 
lean_dec_ref(v___y_671_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_b_670_);
lean_ctor_set(v___x_685_, 1, v___y_672_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* v_as_686_, lean_object* v_i_687_, lean_object* v_stop_688_, lean_object* v_b_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
size_t v_i_boxed_692_; size_t v_stop_boxed_693_; lean_object* v_res_694_; 
v_i_boxed_692_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_stop_boxed_693_ = lean_unbox_usize(v_stop_688_);
lean_dec(v_stop_688_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_686_, v_i_boxed_692_, v_stop_boxed_693_, v_b_689_, v___y_690_, v___y_691_);
lean_dec_ref(v_as_686_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* v_as_695_, lean_object* v_i_696_, lean_object* v_stop_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_i_boxed_701_; size_t v_stop_boxed_702_; lean_object* v_res_703_; 
v_i_boxed_701_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_stop_boxed_702_ = lean_unbox_usize(v_stop_697_);
lean_dec(v_stop_697_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_695_, v_i_boxed_701_, v_stop_boxed_702_, v_b_698_, v___y_699_, v___y_700_);
lean_dec_ref(v_as_695_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* v_00_u03b1_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_705_, v___y_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* v_00_u03b1_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(v_00_u03b1_708_, v___y_709_, v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_711_;
}
}
lean_object* runtime_initialize_Lean_Elab_AutoBound(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_AutoBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Level_maxUniverseOffset = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_AutoBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Level(builtin);
}
#ifdef __cplusplus
}
#endif
