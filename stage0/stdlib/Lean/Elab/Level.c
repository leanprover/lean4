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
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value)} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1 = (const lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value),((lean_object*)&l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value)} };
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
static const lean_closure_object l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value),((lean_object*)&l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value)} };
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
lean_object* v_options_51_; uint8_t v_autoBoundImplicit_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_options_51_ = lean_ctor_get(v___y_49_, 0);
v_autoBoundImplicit_52_ = lean_ctor_get_uint8(v___y_49_, sizeof(void*)*2);
lean_inc_ref(v_options_51_);
v___x_53_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_53_, 0, v_options_51_);
lean_ctor_set(v___x_53_, 1, v_ref_47_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*2, v_autoBoundImplicit_52_);
v___x_54_ = lean_apply_2(v_x_48_, v___x_53_, v___y_50_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed(lean_object* v_00_u03b1_55_, lean_object* v_ref_56_, lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(v_00_u03b1_55_, v_ref_56_, v_x_57_, v___y_58_, v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object* v_msg_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v_msg_71_);
lean_ctor_set(v___x_74_, 1, v___y_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(v_msg_75_, v___y_76_, v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_83_; 
lean_inc_ref(v___y_82_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___y_82_);
lean_ctor_set(v___x_83_, 1, v___y_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(v___y_84_, v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object* v_____do__lift_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_ngen_90_; lean_object* v___x_91_; 
v_ngen_90_ = lean_ctor_get(v_____do__lift_87_, 0);
lean_inc_ref(v_ngen_90_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_ngen_90_);
lean_ctor_set(v___x_91_, 1, v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object* v_____do__lift_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(v_____do__lift_92_, v___y_93_, v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_____do__lift_92_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object* v_ngen_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_mctx_99_; lean_object* v_levelNames_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_109_; 
v_mctx_99_ = lean_ctor_get(v___y_98_, 1);
v_levelNames_100_ = lean_ctor_get(v___y_98_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v___y_98_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v___y_98_, 0);
lean_dec(v_unused_110_);
v___x_102_ = v___y_98_;
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_levelNames_100_);
lean_inc(v_mctx_99_);
lean_dec(v___y_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_box(0);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_ngen_96_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_ngen_96_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_mctx_99_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_levelNames_100_);
v___x_106_ = v_reuseFailAlloc_108_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object* v_ngen_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(v_ngen_111_, v___y_112_, v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object* v___y_126_){
_start:
{
lean_object* v_ngen_127_; lean_object* v_mctx_128_; lean_object* v_levelNames_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_149_; 
v_ngen_127_ = lean_ctor_get(v___y_126_, 0);
v_mctx_128_ = lean_ctor_get(v___y_126_, 1);
v_levelNames_129_ = lean_ctor_get(v___y_126_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v___y_126_);
if (v_isSharedCheck_149_ == 0)
{
v___x_131_ = v___y_126_;
v_isShared_132_ = v_isSharedCheck_149_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_levelNames_129_);
lean_inc(v_mctx_128_);
lean_inc(v_ngen_127_);
lean_dec(v___y_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_149_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_namePrefix_133_; lean_object* v_idx_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_148_; 
v_namePrefix_133_ = lean_ctor_get(v_ngen_127_, 0);
v_idx_134_ = lean_ctor_get(v_ngen_127_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_ngen_127_);
if (v_isSharedCheck_148_ == 0)
{
v___x_136_ = v_ngen_127_;
v_isShared_137_ = v_isSharedCheck_148_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_idx_134_);
lean_inc(v_namePrefix_133_);
lean_dec(v_ngen_127_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_148_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_r_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_inc(v_idx_134_);
lean_inc(v_namePrefix_133_);
v_r_138_ = l_Lean_Name_num___override(v_namePrefix_133_, v_idx_134_);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_idx_134_, v___x_139_);
lean_dec(v_idx_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_140_);
v___x_142_ = v___x_136_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_namePrefix_133_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_147_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_142_);
v___x_144_ = v___x_131_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_mctx_128_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_levelNames_129_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_r_138_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v___x_152_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_151_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_a_154_ = lean_ctor_get(v___x_152_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_152_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v___y_162_, v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v_a_165_, v_a_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_188_; 
v_a_168_ = lean_ctor_get(v___x_167_, 1);
v_a_169_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_188_ == 0)
{
v___x_171_ = v___x_167_;
v_isShared_172_ = v_isSharedCheck_188_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_168_);
lean_inc(v_a_169_);
lean_dec(v___x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_188_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_ngen_173_; lean_object* v_mctx_174_; lean_object* v_levelNames_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_187_; 
v_ngen_173_ = lean_ctor_get(v_a_168_, 0);
v_mctx_174_ = lean_ctor_get(v_a_168_, 1);
v_levelNames_175_ = lean_ctor_get(v_a_168_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_187_ == 0)
{
v___x_177_ = v_a_168_;
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_levelNames_175_);
lean_inc(v_mctx_174_);
lean_inc(v_ngen_173_);
lean_dec(v_a_168_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
lean_inc(v_a_169_);
v___x_179_ = l_Lean_MetavarContext_addLevelMVarDecl(v_mctx_174_, v_a_169_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_ngen_173_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_levelNames_175_);
v___x_181_ = v_reuseFailAlloc_186_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = l_Lean_mkLevelMVar(v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_181_);
lean_ctor_set(v___x_171_, 0, v___x_182_);
v___x_184_ = v___x_171_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_181_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_189_ = lean_ctor_get(v___x_167_, 0);
v_a_190_ = lean_ctor_get(v___x_167_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_167_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_inc(v_a_189_);
lean_dec(v___x_167_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_Level_mkFreshLevelMVar(v_a_198_, v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(v___y_204_, v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* v_name_207_, lean_object* v_decl_208_, lean_object* v_ref_209_){
_start:
{
lean_object* v_defValue_211_; lean_object* v_descr_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_238_; 
v_defValue_211_ = lean_ctor_get(v_decl_208_, 0);
v_descr_212_ = lean_ctor_get(v_decl_208_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_decl_208_);
if (v_isSharedCheck_238_ == 0)
{
v___x_214_ = v_decl_208_;
v_isShared_215_ = v_isSharedCheck_238_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_descr_212_);
lean_inc(v_defValue_211_);
lean_dec(v_decl_208_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_238_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_inc(v_defValue_211_);
v___x_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_216_, 0, v_defValue_211_);
lean_inc_n(v_name_207_, 2);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v_name_207_);
lean_ctor_set(v___x_217_, 1, v_ref_209_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_ctor_set(v___x_217_, 3, v_descr_212_);
v___x_218_ = lean_register_option(v_name_207_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_228_; 
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_218_, 0);
lean_dec(v_unused_229_);
v___x_220_ = v___x_218_;
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
else
{
lean_dec(v___x_218_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_228_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v_defValue_211_);
lean_ctor_set(v___x_214_, 0, v_name_207_);
v___x_223_ = v___x_214_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_name_207_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_defValue_211_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_del_object(v___x_214_);
lean_dec(v_defValue_211_);
lean_dec(v_name_207_);
v_a_230_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_218_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_218_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_239_, lean_object* v_decl_240_, lean_object* v_ref_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_239_, v_decl_240_, v_ref_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_261_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_262_ = ((lean_object*)(l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_263_ = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v___x_260_, v___x_261_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
return v_res_265_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0));
v___x_268_ = l_Lean_stringToMessageData(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6));
v___x_277_ = l_Lean_stringToMessageData(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7);
v___x_279_ = l_Lean_MessageData_note(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object* v___x_280_, lean_object* v_n_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_toApplicative_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v___x_286_; lean_object* v_max_287_; uint8_t v___x_288_; 
v___x_286_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_287_ = l_Lean_Option_get___redArg(v___x_280_, v_____do__lift_285_, v___x_286_);
v___x_288_ = lean_nat_dec_le(v_n_281_, v_max_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref(v_toApplicative_284_);
v___x_289_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_290_ = l_Nat_reprFast(v_n_281_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = l_Lean_MessageData_ofFormat(v___x_291_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_289_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Nat_reprFast(v_max_287_);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = l_Lean_MessageData_ofFormat(v___x_297_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_295_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Lean_throwError___redArg(v_inst_282_, v_inst_283_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_toPure_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_max_287_);
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
lean_dec(v_n_281_);
v_toPure_305_ = lean_ctor_get(v_toApplicative_284_, 1);
lean_inc(v_toPure_305_);
lean_dec_ref(v_toApplicative_284_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_apply_2(v_toPure_305_, lean_box(0), v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* v___x_308_, lean_object* v_n_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_toApplicative_312_, lean_object* v_____do__lift_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(v___x_308_, v_n_309_, v_inst_310_, v_inst_311_, v_toApplicative_312_, v_____do__lift_313_);
lean_dec_ref(v_____do__lift_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_n_318_){
_start:
{
lean_object* v___x_319_; lean_object* v_toApplicative_320_; lean_object* v_toBind_321_; lean_object* v___f_322_; lean_object* v___x_323_; 
v___x_319_ = l_Lean_KVMap_instValueNat;
v_toApplicative_320_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_ref(v_toApplicative_320_);
v_toBind_321_ = lean_ctor_get(v_inst_315_, 1);
lean_inc(v_toBind_321_);
v___f_322_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_322_, 0, v___x_319_);
lean_closure_set(v___f_322_, 1, v_n_318_);
lean_closure_set(v___f_322_, 2, v_inst_315_);
lean_closure_set(v___f_322_, 3, v_inst_316_);
lean_closure_set(v___f_322_, 4, v_toApplicative_320_);
v___x_323_ = lean_apply_4(v_toBind_321_, lean_box(0), lean_box(0), v_inst_317_, v___f_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* v_m_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_n_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(v_inst_325_, v_inst_326_, v_inst_327_, v_n_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_ref_333_ = lean_ctor_get(v___y_331_, 1);
lean_inc(v_ref_333_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_333_);
lean_ctor_set(v___x_334_, 1, v_msg_330_);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___y_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_336_, v___y_337_, v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object* v_00_u03b1_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_341_, v___y_342_, v___y_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* v_00_u03b1_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(v_00_u03b1_345_, v_msg_346_, v___y_347_, v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object* v_opts_350_, lean_object* v_opt_351_){
_start:
{
lean_object* v_name_352_; lean_object* v_defValue_353_; lean_object* v_map_354_; lean_object* v___x_355_; 
v_name_352_ = lean_ctor_get(v_opt_351_, 0);
v_defValue_353_ = lean_ctor_get(v_opt_351_, 1);
v_map_354_ = lean_ctor_get(v_opts_350_, 0);
v___x_355_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_354_, v_name_352_);
if (lean_obj_tag(v___x_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = lean_unbox(v_defValue_353_);
return v___x_356_;
}
else
{
lean_object* v_val_357_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref(v___x_355_);
if (lean_obj_tag(v_val_357_) == 1)
{
uint8_t v_v_358_; 
v_v_358_ = lean_ctor_get_uint8(v_val_357_, 0);
lean_dec_ref(v_val_357_);
return v_v_358_;
}
else
{
uint8_t v___x_359_; 
lean_dec(v_val_357_);
v___x_359_ = lean_unbox(v_defValue_353_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* v_opts_360_, lean_object* v_opt_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_360_, v_opt_361_);
lean_dec_ref(v_opt_361_);
lean_dec_ref(v_opts_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
v___x_370_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_369_, v___y_367_, v___y_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_371_, v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_373_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(lean_object* v_a_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
uint8_t v___x_376_; 
v___x_376_ = 0;
return v___x_376_;
}
else
{
lean_object* v_head_377_; lean_object* v_tail_378_; uint8_t v___x_379_; 
v_head_377_ = lean_ctor_get(v_x_375_, 0);
v_tail_378_ = lean_ctor_get(v_x_375_, 1);
v___x_379_ = lean_name_eq(v_a_374_, v_head_377_);
if (v___x_379_ == 0)
{
v_x_375_ = v_tail_378_;
goto _start;
}
else
{
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object* v_a_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_381_, v_x_382_);
lean_dec(v_x_382_);
lean_dec(v_a_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* v_opts_385_, lean_object* v_opt_386_){
_start:
{
lean_object* v_name_387_; lean_object* v_defValue_388_; lean_object* v_map_389_; lean_object* v___x_390_; 
v_name_387_ = lean_ctor_get(v_opt_386_, 0);
v_defValue_388_ = lean_ctor_get(v_opt_386_, 1);
v_map_389_ = lean_ctor_get(v_opts_385_, 0);
v___x_390_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_389_, v_name_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_inc(v_defValue_388_);
return v_defValue_388_;
}
else
{
lean_object* v_val_391_; 
v_val_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_391_);
lean_dec_ref(v___x_390_);
if (lean_obj_tag(v_val_391_) == 3)
{
lean_object* v_v_392_; 
v_v_392_ = lean_ctor_get(v_val_391_, 0);
lean_inc(v_v_392_);
lean_dec_ref(v_val_391_);
return v_v_392_;
}
else
{
lean_dec(v_val_391_);
lean_inc(v_defValue_388_);
return v_defValue_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* v_opts_393_, lean_object* v_opt_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_opts_393_, v_opt_394_);
lean_dec_ref(v_opt_394_);
lean_dec_ref(v_opts_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object* v_n_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_options_399_; lean_object* v___x_400_; lean_object* v_max_401_; uint8_t v___x_402_; 
v_options_399_ = lean_ctor_get(v___y_397_, 0);
v___x_400_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_401_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_options_399_, v___x_400_);
v___x_402_ = lean_nat_dec_le(v_n_396_, v_max_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_403_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_404_ = l_Nat_reprFast(v_n_396_);
v___x_405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___x_406_ = l_Lean_MessageData_ofFormat(v___x_405_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_403_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Nat_reprFast(v_max_401_);
v___x_411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
v___x_412_ = l_Lean_MessageData_ofFormat(v___x_411_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_409_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_417_, v___y_397_, v___y_398_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_max_401_);
lean_dec(v_n_396_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___y_398_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* v_n_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_n_421_, v___y_422_, v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_424_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__15));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__17));
v___x_467_ = l_Lean_stringToMessageData(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object* v_as_468_, size_t v_i_469_, size_t v_stop_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_eq(v_i_469_, v_stop_470_);
if (v___x_474_ == 0)
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v_i_469_, v___x_475_);
v___x_477_ = lean_array_uget_borrowed(v_as_468_, v___x_476_);
lean_inc_ref(v___y_472_);
lean_inc(v___x_477_);
v___x_478_ = l_Lean_Elab_Level_elabLevel(v___x_477_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
v_a_480_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_a_480_);
lean_dec_ref(v___x_478_);
v___x_481_ = l_Lean_mkLevelMax_x27(v_a_479_, v_b_471_);
v_i_469_ = v___x_476_;
v_b_471_ = v___x_481_;
v___y_473_ = v_a_480_;
goto _start;
}
else
{
lean_dec(v_b_471_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_483_; lean_object* v_a_484_; 
v_a_483_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_483_);
v_a_484_ = lean_ctor_get(v___x_478_, 1);
lean_inc(v_a_484_);
lean_dec_ref(v___x_478_);
v_i_469_ = v___x_476_;
v_b_471_ = v_a_483_;
v___y_473_ = v_a_484_;
goto _start;
}
else
{
return v___x_478_;
}
}
}
else
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_b_471_);
lean_ctor_set(v___x_486_, 1, v___y_473_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* v_stx_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_options_490_; lean_object* v_ref_491_; uint8_t v_autoBoundImplicit_492_; lean_object* v_kind_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v_ref_496_; lean_object* v___x_497_; 
v_options_490_ = lean_ctor_get(v_a_488_, 0);
lean_inc_ref_n(v_options_490_, 2);
v_ref_491_ = lean_ctor_get(v_a_488_, 1);
lean_inc(v_ref_491_);
v_autoBoundImplicit_492_ = lean_ctor_get_uint8(v_a_488_, sizeof(void*)*2);
lean_dec_ref(v_a_488_);
lean_inc(v_stx_487_);
v_kind_493_ = l_Lean_Syntax_getKind(v_stx_487_);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__2));
v___x_495_ = lean_name_eq(v_kind_493_, v___x_494_);
v_ref_496_ = l_Lean_replaceRef(v_stx_487_, v_ref_491_);
lean_dec(v_ref_491_);
v___x_497_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_497_, 0, v_options_490_);
lean_ctor_set(v___x_497_, 1, v_ref_496_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*2, v_autoBoundImplicit_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__4));
v___x_499_ = lean_name_eq(v_kind_493_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__6));
v___x_501_ = lean_name_eq(v_kind_493_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__8));
v___x_503_ = lean_name_eq(v_kind_493_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__10));
v___x_505_ = lean_name_eq(v_kind_493_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__12));
v___x_507_ = lean_name_eq(v_kind_493_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
lean_dec_ref(v_options_490_);
v___x_508_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__14));
v___x_509_ = lean_name_eq(v_kind_493_, v___x_508_);
lean_dec(v_kind_493_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_stx_487_);
v___x_510_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__16, &l_Lean_Elab_Level_elabLevel___closed__16_once, _init_l_Lean_Elab_Level_elabLevel___closed__16);
v___x_511_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_510_, v___x_497_, v_a_489_);
lean_dec_ref(v___x_497_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_Syntax_getArg(v_stx_487_, v___x_512_);
lean_inc_ref(v___x_497_);
v___x_514_ = l_Lean_Elab_Level_elabLevel(v___x_513_, v___x_497_, v_a_489_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
v_a_516_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_a_516_);
lean_dec_ref(v___x_514_);
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = l_Lean_Syntax_getArg(v_stx_487_, v___x_517_);
lean_dec(v_stx_487_);
v___x_519_ = l_Lean_Syntax_isNatLit_x3f(v___x_518_);
lean_dec(v___x_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
lean_dec(v_a_515_);
v___x_520_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_497_, v_a_516_);
lean_dec_ref(v___x_497_);
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; 
v_val_521_ = lean_ctor_get(v___x_519_, 0);
lean_inc_n(v_val_521_, 2);
lean_dec_ref(v___x_519_);
v___x_522_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_521_, v___x_497_, v_a_516_);
lean_dec_ref(v___x_497_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_a_523_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_532_);
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = l_Lean_Level_addOffset(v_a_515_, v_val_521_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_523_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_val_521_);
lean_dec(v_a_515_);
v_a_533_ = lean_ctor_get(v___x_522_, 0);
v_a_534_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_522_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_inc(v_a_533_);
lean_dec(v___x_522_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_533_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_497_);
lean_dec(v_stx_487_);
return v___x_514_;
}
}
}
else
{
lean_object* v_ngen_542_; lean_object* v_mctx_543_; lean_object* v_levelNames_544_; lean_object* v_paramName_545_; lean_object* v___y_547_; uint8_t v___x_568_; 
lean_dec(v_kind_493_);
v_ngen_542_ = lean_ctor_get(v_a_489_, 0);
v_mctx_543_ = lean_ctor_get(v_a_489_, 1);
v_levelNames_544_ = lean_ctor_get(v_a_489_, 2);
v_paramName_545_ = l_Lean_Syntax_getId(v_stx_487_);
lean_dec(v_stx_487_);
v___x_568_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_paramName_545_, v_levelNames_544_);
if (v___x_568_ == 0)
{
if (v_autoBoundImplicit_492_ == 0)
{
lean_dec_ref(v_options_490_);
goto v___jp_550_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; uint8_t v___x_571_; 
v___x_569_ = l_Lean_Elab_relaxedAutoImplicit;
v___x_570_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_490_, v___x_569_);
lean_dec_ref(v_options_490_);
lean_inc(v_paramName_545_);
v___x_571_ = l_Lean_Elab_isValidAutoBoundLevelName(v_paramName_545_, v___x_570_);
if (v___x_571_ == 0)
{
goto v___jp_550_;
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
lean_inc(v_levelNames_544_);
lean_inc_ref(v_mctx_543_);
lean_inc_ref(v_ngen_542_);
lean_dec_ref(v___x_497_);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_580_ = lean_ctor_get(v_a_489_, 2);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_a_489_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_a_489_, 0);
lean_dec(v_unused_582_);
v___x_573_ = v_a_489_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_a_489_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_paramName_545_);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v_paramName_545_);
lean_ctor_set(v___x_575_, 1, v_levelNames_544_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 2, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_mctx_543_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_547_ = v___x_577_;
goto v___jp_546_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_497_);
lean_dec_ref(v_options_490_);
v___y_547_ = v_a_489_;
goto v___jp_546_;
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_mkLevelParam(v_paramName_545_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___y_547_);
return v___x_549_;
}
v___jp_550_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_551_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__18, &l_Lean_Elab_Level_elabLevel___closed__18_once, _init_l_Lean_Elab_Level_elabLevel___closed__18);
lean_inc(v_paramName_545_);
v___x_552_ = lean_mk_syntax_ident(v_paramName_545_);
v___x_553_ = l_Lean_MessageData_ofSyntax(v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_556_, v___x_497_, v_a_489_);
lean_dec_ref(v___x_497_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; 
v_a_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_a_558_);
lean_dec_ref(v___x_557_);
v___y_547_ = v_a_558_;
goto v___jp_546_;
}
else
{
lean_object* v_a_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_paramName_545_);
v_a_559_ = lean_ctor_get(v___x_557_, 0);
v_a_560_ = lean_ctor_get(v___x_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_557_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_inc(v_a_559_);
lean_dec(v___x_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_559_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v_kind_493_);
lean_dec_ref(v_options_490_);
v___x_583_ = l_Lean_Syntax_isNatLit_x3f(v_stx_487_);
lean_dec(v_stx_487_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_497_, v_a_489_);
lean_dec_ref(v___x_497_);
return v___x_584_;
}
else
{
lean_object* v_val_585_; lean_object* v___x_586_; 
v_val_585_ = lean_ctor_get(v___x_583_, 0);
lean_inc_n(v_val_585_, 2);
lean_dec_ref(v___x_583_);
v___x_586_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_585_, v___x_497_, v_a_489_);
lean_dec_ref(v___x_497_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_a_587_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_596_);
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_Level_ofNat(v_val_585_);
lean_dec(v_val_585_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_587_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_val_585_);
v_a_597_ = lean_ctor_get(v___x_586_, 0);
v_a_598_ = lean_ctor_get(v___x_586_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_586_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_inc(v_a_597_);
lean_dec(v___x_586_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
else
{
lean_object* v___x_606_; 
lean_dec(v_kind_493_);
lean_dec_ref(v_options_490_);
lean_dec(v_stx_487_);
v___x_606_ = l_Lean_Elab_Level_mkFreshLevelMVar(v___x_497_, v_a_489_);
lean_dec_ref(v___x_497_);
return v___x_606_;
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_args_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_kind_493_);
lean_dec_ref(v_options_490_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = l_Lean_Syntax_getArg(v_stx_487_, v___x_607_);
lean_dec(v_stx_487_);
v_args_609_ = l_Lean_Syntax_getArgs(v___x_608_);
lean_dec(v___x_608_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_array_get_size(v_args_609_);
v___x_612_ = lean_nat_sub(v___x_611_, v___x_607_);
v___x_613_ = lean_array_get(v___x_610_, v_args_609_, v___x_612_);
lean_inc_ref(v___x_497_);
v___x_614_ = l_Lean_Elab_Level_elabLevel(v___x_613_, v___x_497_, v_a_489_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_array_619_; lean_object* v_start_620_; lean_object* v_stop_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Array_toSubarray___redArg(v_args_609_, v___x_617_, v___x_612_);
v_array_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_array_619_);
v_start_620_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_start_620_);
v_stop_621_ = lean_ctor_get(v___x_618_, 2);
lean_inc(v_stop_621_);
lean_dec_ref(v___x_618_);
v___x_622_ = lean_array_get_size(v_array_619_);
v___x_623_ = lean_nat_dec_le(v_stop_621_, v___x_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
lean_dec(v_stop_621_);
v___x_624_ = lean_nat_dec_lt(v_start_620_, v___x_622_);
if (v___x_624_ == 0)
{
lean_dec(v_start_620_);
lean_dec_ref(v_array_619_);
lean_dec(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v___x_497_);
return v___x_614_;
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v___x_614_);
v___x_625_ = lean_usize_of_nat(v___x_622_);
v___x_626_ = lean_usize_of_nat(v_start_620_);
lean_dec(v_start_620_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_619_, v___x_625_, v___x_626_, v_a_615_, v___x_497_, v_a_616_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_array_619_);
return v___x_627_;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_lt(v_start_620_, v_stop_621_);
if (v___x_628_ == 0)
{
lean_dec(v_stop_621_);
lean_dec(v_start_620_);
lean_dec_ref(v_array_619_);
lean_dec(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v___x_497_);
return v___x_614_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v___x_614_);
v___x_629_ = lean_usize_of_nat(v_stop_621_);
lean_dec(v_stop_621_);
v___x_630_ = lean_usize_of_nat(v_start_620_);
lean_dec(v_start_620_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_619_, v___x_629_, v___x_630_, v_a_615_, v___x_497_, v_a_616_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_array_619_);
return v___x_631_;
}
}
}
else
{
lean_dec(v___x_612_);
lean_dec_ref(v_args_609_);
lean_dec_ref(v___x_497_);
return v___x_614_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_args_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_kind_493_);
lean_dec_ref(v_options_490_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = l_Lean_Syntax_getArg(v_stx_487_, v___x_632_);
lean_dec(v_stx_487_);
v_args_634_ = l_Lean_Syntax_getArgs(v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_array_get_size(v_args_634_);
v___x_637_ = lean_nat_sub(v___x_636_, v___x_632_);
v___x_638_ = lean_array_get(v___x_635_, v_args_634_, v___x_637_);
lean_inc_ref(v___x_497_);
v___x_639_ = l_Lean_Elab_Level_elabLevel(v___x_638_, v___x_497_, v_a_489_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_array_644_; lean_object* v_start_645_; lean_object* v_stop_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
v_a_641_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_a_641_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = l_Array_toSubarray___redArg(v_args_634_, v___x_642_, v___x_637_);
v_array_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_array_644_);
v_start_645_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_start_645_);
v_stop_646_ = lean_ctor_get(v___x_643_, 2);
lean_inc(v_stop_646_);
lean_dec_ref(v___x_643_);
v___x_647_ = lean_array_get_size(v_array_644_);
v___x_648_ = lean_nat_dec_le(v_stop_646_, v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
lean_dec(v_stop_646_);
v___x_649_ = lean_nat_dec_lt(v_start_645_, v___x_647_);
if (v___x_649_ == 0)
{
lean_dec(v_start_645_);
lean_dec_ref(v_array_644_);
lean_dec(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v___x_497_);
return v___x_639_;
}
else
{
size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v___x_639_);
v___x_650_ = lean_usize_of_nat(v___x_647_);
v___x_651_ = lean_usize_of_nat(v_start_645_);
lean_dec(v_start_645_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_644_, v___x_650_, v___x_651_, v_a_640_, v___x_497_, v_a_641_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_array_644_);
return v___x_652_;
}
}
else
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_lt(v_start_645_, v_stop_646_);
if (v___x_653_ == 0)
{
lean_dec(v_stop_646_);
lean_dec(v_start_645_);
lean_dec_ref(v_array_644_);
lean_dec(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v___x_497_);
return v___x_639_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
lean_dec_ref(v___x_639_);
v___x_654_ = lean_usize_of_nat(v_stop_646_);
lean_dec(v_stop_646_);
v___x_655_ = lean_usize_of_nat(v_start_645_);
lean_dec(v_start_645_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_644_, v___x_654_, v___x_655_, v_a_640_, v___x_497_, v_a_641_);
lean_dec_ref(v___x_497_);
lean_dec_ref(v_array_644_);
return v___x_656_;
}
}
}
else
{
lean_dec(v___x_637_);
lean_dec_ref(v_args_634_);
lean_dec_ref(v___x_497_);
return v___x_639_;
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v_kind_493_);
lean_dec_ref(v_options_490_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = l_Lean_Syntax_getArg(v_stx_487_, v___x_657_);
lean_dec(v_stx_487_);
v_stx_487_ = v___x_658_;
v_a_488_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* v_as_660_, size_t v_i_661_, size_t v_stop_662_, lean_object* v_b_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_eq(v_i_661_, v_stop_662_);
if (v___x_666_ == 0)
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_sub(v_i_661_, v___x_667_);
v___x_669_ = lean_array_uget_borrowed(v_as_660_, v___x_668_);
lean_inc_ref(v___y_664_);
lean_inc(v___x_669_);
v___x_670_ = l_Lean_Elab_Level_elabLevel(v___x_669_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
v_a_672_ = lean_ctor_get(v___x_670_, 1);
lean_inc(v_a_672_);
lean_dec_ref(v___x_670_);
v___x_673_ = l_Lean_mkLevelIMax_x27(v_a_671_, v_b_663_);
v_i_661_ = v___x_668_;
v_b_663_ = v___x_673_;
v___y_665_ = v_a_672_;
goto _start;
}
else
{
lean_dec(v_b_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_675_; lean_object* v_a_676_; 
v_a_675_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_675_);
v_a_676_ = lean_ctor_get(v___x_670_, 1);
lean_inc(v_a_676_);
lean_dec_ref(v___x_670_);
v_i_661_ = v___x_668_;
v_b_663_ = v_a_675_;
v___y_665_ = v_a_676_;
goto _start;
}
else
{
return v___x_670_;
}
}
}
else
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_b_663_);
lean_ctor_set(v___x_678_, 1, v___y_665_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_i_boxed_685_; size_t v_stop_boxed_686_; lean_object* v_res_687_; 
v_i_boxed_685_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_686_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_679_, v_i_boxed_685_, v_stop_boxed_686_, v_b_682_, v___y_683_, v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* v_as_688_, lean_object* v_i_689_, lean_object* v_stop_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
size_t v_i_boxed_694_; size_t v_stop_boxed_695_; lean_object* v_res_696_; 
v_i_boxed_694_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_stop_boxed_695_ = lean_unbox_usize(v_stop_690_);
lean_dec(v_stop_690_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_688_, v_i_boxed_694_, v_stop_boxed_695_, v_b_691_, v___y_692_, v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_as_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* v_00_u03b1_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_698_, v___y_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* v_00_u03b1_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(v_00_u03b1_701_, v___y_702_, v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_704_;
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
