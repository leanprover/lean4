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
lean_object* l_EStateM_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* l_EStateM_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value;
static const lean_closure_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EStateM_instMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value),((lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value)}};
static const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__13 = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM = (const lean_object*)&l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__13_value;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "maxUniverseOffset"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(239, 24, 201, 205, 109, 178, 222, 7)}};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "maximum universe level offset"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(223, 205, 225, 18, 63, 191, 162, 209)}};
static const lean_ctor_object l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 128, 181, 12, 212, 155, 25, 154)}};
static const lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 57, 231, 14, 244, 115, 229)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__2 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__2_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__3 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 181, 1, 145, 170, 142, 100, 97)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__4 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__4_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__5 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 169, 176, 27, 219, 169, 119, 28)}};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__6 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__6_value;
static const lean_string_object l_Lean_Elab_Level_elabLevel___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Level_elabLevel___closed__7 = (const lean_object*)&l_Lean_Elab_Level_elabLevel___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
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
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Level_elabLevel___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(176, 210, 143, 23, 235, 250, 136, 158)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object* v_____do__lift_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_ref_42_; lean_object* v___x_43_; 
v_ref_42_ = lean_ctor_get(v_____do__lift_39_, 1);
lean_inc(v_ref_42_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v_ref_42_);
lean_ctor_set(v___x_43_, 1, v___y_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object* v_____do__lift_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(v_____do__lift_44_, v___y_45_, v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec_ref(v_____do__lift_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object* v_00_u03b1_48_, lean_object* v_ref_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_options_53_; uint8_t v_autoBoundImplicit_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_options_53_ = lean_ctor_get(v___y_51_, 0);
v_autoBoundImplicit_54_ = lean_ctor_get_uint8(v___y_51_, sizeof(void*)*2);
lean_inc_ref(v_options_53_);
v___x_55_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_55_, 0, v_options_53_);
lean_ctor_set(v___x_55_, 1, v_ref_49_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*2, v_autoBoundImplicit_54_);
v___x_56_ = lean_apply_2(v_x_50_, v___x_55_, v___y_52_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed(lean_object* v_00_u03b1_57_, lean_object* v_ref_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(v_00_u03b1_57_, v_ref_58_, v_x_59_, v___y_60_, v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object* v_msg_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_msg_73_);
lean_ctor_set(v___x_76_, 1, v___y_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(v_msg_77_, v___y_78_, v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_85_; 
lean_inc_ref(v___y_84_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_84_);
lean_ctor_set(v___x_85_, 1, v___y_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(v___y_86_, v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object* v_____do__lift_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_ngen_92_; lean_object* v___x_93_; 
v_ngen_92_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc_ref(v_ngen_92_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_ngen_92_);
lean_ctor_set(v___x_93_, 1, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object* v_____do__lift_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(v_____do__lift_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec_ref(v_____do__lift_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object* v_ngen_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_mctx_101_; lean_object* v_levelNames_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_111_; 
v_mctx_101_ = lean_ctor_get(v___y_100_, 1);
v_levelNames_102_ = lean_ctor_get(v___y_100_, 2);
v_isSharedCheck_111_ = !lean_is_exclusive(v___y_100_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___y_100_, 0);
lean_dec(v_unused_112_);
v___x_104_ = v___y_100_;
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_levelNames_102_);
lean_inc(v_mctx_101_);
lean_dec(v___y_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_111_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_ngen_98_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_mctx_101_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_levelNames_102_);
v___x_108_ = v_reuseFailAlloc_110_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object* v_ngen_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(v_ngen_113_, v___y_114_, v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object* v___y_128_){
_start:
{
lean_object* v_ngen_129_; lean_object* v_mctx_130_; lean_object* v_levelNames_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_151_; 
v_ngen_129_ = lean_ctor_get(v___y_128_, 0);
v_mctx_130_ = lean_ctor_get(v___y_128_, 1);
v_levelNames_131_ = lean_ctor_get(v___y_128_, 2);
v_isSharedCheck_151_ = !lean_is_exclusive(v___y_128_);
if (v_isSharedCheck_151_ == 0)
{
v___x_133_ = v___y_128_;
v_isShared_134_ = v_isSharedCheck_151_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_levelNames_131_);
lean_inc(v_mctx_130_);
lean_inc(v_ngen_129_);
lean_dec(v___y_128_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_151_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_namePrefix_135_; lean_object* v_idx_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_150_; 
v_namePrefix_135_ = lean_ctor_get(v_ngen_129_, 0);
v_idx_136_ = lean_ctor_get(v_ngen_129_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_ngen_129_);
if (v_isSharedCheck_150_ == 0)
{
v___x_138_ = v_ngen_129_;
v_isShared_139_ = v_isSharedCheck_150_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_idx_136_);
lean_inc(v_namePrefix_135_);
lean_dec(v_ngen_129_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_150_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_r_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc(v_idx_136_);
lean_inc(v_namePrefix_135_);
v_r_140_ = l_Lean_Name_num___override(v_namePrefix_135_, v_idx_136_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_add(v_idx_136_, v___x_141_);
lean_dec(v_idx_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_142_);
v___x_144_ = v___x_138_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_namePrefix_135_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_149_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_144_);
v___x_146_ = v___x_133_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_mctx_130_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_levelNames_131_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_r_140_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v___x_154_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_153_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_a_156_ = lean_ctor_get(v___x_154_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_154_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v___y_164_, v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_190_; 
v_a_170_ = lean_ctor_get(v___x_169_, 1);
v_a_171_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_190_ == 0)
{
v___x_173_ = v___x_169_;
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_170_);
lean_inc(v_a_171_);
lean_dec(v___x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_ngen_175_; lean_object* v_mctx_176_; lean_object* v_levelNames_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_189_; 
v_ngen_175_ = lean_ctor_get(v_a_170_, 0);
v_mctx_176_ = lean_ctor_get(v_a_170_, 1);
v_levelNames_177_ = lean_ctor_get(v_a_170_, 2);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_170_);
if (v_isSharedCheck_189_ == 0)
{
v___x_179_ = v_a_170_;
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_levelNames_177_);
lean_inc(v_mctx_176_);
lean_inc(v_ngen_175_);
lean_dec(v_a_170_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_inc(v_a_171_);
v___x_181_ = l_Lean_MetavarContext_addLevelMVarDecl(v_mctx_176_, v_a_171_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_ngen_175_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_levelNames_177_);
v___x_183_ = v_reuseFailAlloc_188_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = l_Lean_mkLevelMVar(v_a_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_183_);
lean_ctor_set(v___x_173_, 0, v___x_184_);
v___x_186_ = v___x_173_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_183_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_191_ = lean_ctor_get(v___x_169_, 0);
v_a_192_ = lean_ctor_get(v___x_169_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_169_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_inc(v_a_191_);
lean_dec(v___x_169_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Elab_Level_mkFreshLevelMVar(v_a_200_, v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(v___y_206_, v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* v_name_209_, lean_object* v_decl_210_, lean_object* v_ref_211_){
_start:
{
lean_object* v_defValue_213_; lean_object* v_descr_214_; lean_object* v_deprecation_x3f_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_defValue_213_ = lean_ctor_get(v_decl_210_, 0);
v_descr_214_ = lean_ctor_get(v_decl_210_, 1);
v_deprecation_x3f_215_ = lean_ctor_get(v_decl_210_, 2);
lean_inc(v_defValue_213_);
v___x_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_216_, 0, v_defValue_213_);
lean_inc(v_deprecation_x3f_215_);
lean_inc_ref(v_descr_214_);
lean_inc_n(v_name_209_, 2);
v___x_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_217_, 0, v_name_209_);
lean_ctor_set(v___x_217_, 1, v_ref_211_);
lean_ctor_set(v___x_217_, 2, v___x_216_);
lean_ctor_set(v___x_217_, 3, v_descr_214_);
lean_ctor_set(v___x_217_, 4, v_deprecation_x3f_215_);
v___x_218_ = lean_register_option(v_name_209_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_218_, 0);
lean_dec(v_unused_227_);
v___x_220_ = v___x_218_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_dec(v___x_218_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_defValue_213_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_name_209_);
lean_ctor_set(v___x_222_, 1, v_defValue_213_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_name_209_);
v_a_228_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_218_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_236_, lean_object* v_decl_237_, lean_object* v_ref_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_236_, v_decl_237_, v_ref_238_);
lean_dec_ref(v_decl_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_261_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v___x_258_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
return v_res_263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7);
v___x_277_ = l_Lean_MessageData_note(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object* v___x_278_, lean_object* v_n_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_toPure_282_, lean_object* v_____do__lift_283_){
_start:
{
lean_object* v___x_284_; lean_object* v_max_285_; uint8_t v___x_286_; 
v___x_284_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_285_ = l_Lean_Option_get___redArg(v___x_278_, v_____do__lift_283_, v___x_284_);
v___x_286_ = lean_nat_dec_le(v_n_279_, v_max_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_toPure_282_);
v___x_287_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_288_ = l_Nat_reprFast(v_n_279_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = l_Lean_MessageData_ofFormat(v___x_289_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_287_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Nat_reprFast(v_max_285_);
v___x_295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
v___x_296_ = l_Lean_MessageData_ofFormat(v___x_295_);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_293_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_throwError___redArg(v_inst_280_, v_inst_281_, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_max_285_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
lean_dec(v_n_279_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_2(v_toPure_282_, lean_box(0), v___x_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* v___x_305_, lean_object* v_n_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_toPure_309_, lean_object* v_____do__lift_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(v___x_305_, v_n_306_, v_inst_307_, v_inst_308_, v_toPure_309_, v_____do__lift_310_);
lean_dec_ref(v_____do__lift_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_n_315_){
_start:
{
lean_object* v___x_316_; lean_object* v_toApplicative_317_; lean_object* v_toBind_318_; lean_object* v_getOptions_319_; lean_object* v_toPure_320_; lean_object* v___f_321_; lean_object* v___x_322_; 
v___x_316_ = l_Lean_KVMap_instValueNat;
v_toApplicative_317_ = lean_ctor_get(v_inst_312_, 0);
v_toBind_318_ = lean_ctor_get(v_inst_312_, 1);
lean_inc(v_toBind_318_);
v_getOptions_319_ = lean_ctor_get(v_inst_314_, 0);
lean_inc(v_getOptions_319_);
lean_dec_ref(v_inst_314_);
v_toPure_320_ = lean_ctor_get(v_toApplicative_317_, 1);
lean_inc(v_toPure_320_);
v___f_321_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_321_, 0, v___x_316_);
lean_closure_set(v___f_321_, 1, v_n_315_);
lean_closure_set(v___f_321_, 2, v_inst_312_);
lean_closure_set(v___f_321_, 3, v_inst_313_);
lean_closure_set(v___f_321_, 4, v_toPure_320_);
v___x_322_ = lean_apply_4(v_toBind_318_, lean_box(0), lean_box(0), v_getOptions_319_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_n_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(v_inst_324_, v_inst_325_, v_inst_326_, v_n_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_ref_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_ref_332_ = lean_ctor_get(v___y_330_, 1);
lean_inc(v_ref_332_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_ref_332_);
lean_ctor_set(v___x_333_, 1, v_msg_329_);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___y_331_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_335_, v___y_336_, v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object* v_00_u03b1_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v_msg_340_, v___y_341_, v___y_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* v_00_u03b1_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(v_00_u03b1_344_, v_msg_345_, v___y_346_, v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object* v_opts_349_, lean_object* v_opt_350_){
_start:
{
lean_object* v_name_351_; lean_object* v_defValue_352_; lean_object* v_map_353_; lean_object* v___x_354_; 
v_name_351_ = lean_ctor_get(v_opt_350_, 0);
v_defValue_352_ = lean_ctor_get(v_opt_350_, 1);
v_map_353_ = lean_ctor_get(v_opts_349_, 0);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_353_, v_name_351_);
if (lean_obj_tag(v___x_354_) == 0)
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_defValue_352_);
return v___x_355_;
}
else
{
lean_object* v_val_356_; 
v_val_356_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_356_);
lean_dec_ref_known(v___x_354_, 1);
if (lean_obj_tag(v_val_356_) == 1)
{
uint8_t v_v_357_; 
v_v_357_ = lean_ctor_get_uint8(v_val_356_, 0);
lean_dec_ref_known(v_val_356_, 0);
return v_v_357_;
}
else
{
uint8_t v___x_358_; 
lean_dec(v_val_356_);
v___x_358_ = lean_unbox(v_defValue_352_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* v_opts_359_, lean_object* v_opt_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_359_, v_opt_360_);
lean_dec_ref(v_opt_360_);
lean_dec_ref(v_opts_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
v___x_369_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_368_, v___y_366_, v___y_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_370_, v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(lean_object* v_a_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_head_376_; lean_object* v_tail_377_; uint8_t v___x_378_; 
v_head_376_ = lean_ctor_get(v_x_374_, 0);
v_tail_377_ = lean_ctor_get(v_x_374_, 1);
v___x_378_ = lean_name_eq(v_a_373_, v_head_376_);
if (v___x_378_ == 0)
{
v_x_374_ = v_tail_377_;
goto _start;
}
else
{
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object* v_a_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_380_, v_x_381_);
lean_dec(v_x_381_);
lean_dec(v_a_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* v_opts_384_, lean_object* v_opt_385_){
_start:
{
lean_object* v_name_386_; lean_object* v_defValue_387_; lean_object* v_map_388_; lean_object* v___x_389_; 
v_name_386_ = lean_ctor_get(v_opt_385_, 0);
v_defValue_387_ = lean_ctor_get(v_opt_385_, 1);
v_map_388_ = lean_ctor_get(v_opts_384_, 0);
v___x_389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_388_, v_name_386_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_inc(v_defValue_387_);
return v_defValue_387_;
}
else
{
lean_object* v_val_390_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
if (lean_obj_tag(v_val_390_) == 3)
{
lean_object* v_v_391_; 
v_v_391_ = lean_ctor_get(v_val_390_, 0);
lean_inc(v_v_391_);
lean_dec_ref_known(v_val_390_, 1);
return v_v_391_;
}
else
{
lean_dec(v_val_390_);
lean_inc(v_defValue_387_);
return v_defValue_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* v_opts_392_, lean_object* v_opt_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_opts_392_, v_opt_393_);
lean_dec_ref(v_opt_393_);
lean_dec_ref(v_opts_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object* v_n_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_options_398_; lean_object* v___x_399_; lean_object* v_max_400_; uint8_t v___x_401_; 
v_options_398_ = lean_ctor_get(v___y_396_, 0);
v___x_399_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_400_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_options_398_, v___x_399_);
v___x_401_ = lean_nat_dec_le(v_n_395_, v_max_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_402_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_403_ = l_Nat_reprFast(v_n_395_);
v___x_404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = l_Lean_MessageData_ofFormat(v___x_404_);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Nat_reprFast(v_max_400_);
v___x_410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
v___x_411_ = l_Lean_MessageData_ofFormat(v___x_410_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_408_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_416_, v___y_396_, v___y_397_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_max_400_);
lean_dec(v_n_395_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___y_397_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* v_n_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_n_420_, v___y_421_, v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_423_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__15));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__17));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object* v_as_467_, size_t v_i_468_, size_t v_stop_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_eq(v_i_468_, v_stop_469_);
if (v___x_473_ == 0)
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_sub(v_i_468_, v___x_474_);
v___x_476_ = lean_array_uget_borrowed(v_as_467_, v___x_475_);
lean_inc_ref(v___y_471_);
lean_inc(v___x_476_);
v___x_477_ = l_Lean_Elab_Level_elabLevel(v___x_476_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
v_a_479_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_477_, 2);
v___x_480_ = l_Lean_mkLevelMax_x27(v_a_478_, v_b_470_);
v_i_468_ = v___x_475_;
v_b_470_ = v___x_480_;
v___y_472_ = v_a_479_;
goto _start;
}
else
{
lean_dec(v_b_470_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; 
v_a_482_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_482_);
v_a_483_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_477_, 2);
v_i_468_ = v___x_475_;
v_b_470_ = v_a_482_;
v___y_472_ = v_a_483_;
goto _start;
}
else
{
return v___x_477_;
}
}
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_b_470_);
lean_ctor_set(v___x_485_, 1, v___y_472_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* v_stx_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_options_489_; lean_object* v_ref_490_; uint8_t v_autoBoundImplicit_491_; lean_object* v_kind_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v_ref_495_; lean_object* v___x_496_; 
v_options_489_ = lean_ctor_get(v_a_487_, 0);
lean_inc_ref_n(v_options_489_, 2);
v_ref_490_ = lean_ctor_get(v_a_487_, 1);
lean_inc(v_ref_490_);
v_autoBoundImplicit_491_ = lean_ctor_get_uint8(v_a_487_, sizeof(void*)*2);
lean_dec_ref(v_a_487_);
lean_inc(v_stx_486_);
v_kind_492_ = l_Lean_Syntax_getKind(v_stx_486_);
v___x_493_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__2));
v___x_494_ = lean_name_eq(v_kind_492_, v___x_493_);
v_ref_495_ = l_Lean_replaceRef(v_stx_486_, v_ref_490_);
lean_dec(v_ref_490_);
v___x_496_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_496_, 0, v_options_489_);
lean_ctor_set(v___x_496_, 1, v_ref_495_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*2, v_autoBoundImplicit_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_box(0);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__4));
v___x_499_ = lean_name_eq(v_kind_492_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__6));
v___x_501_ = lean_name_eq(v_kind_492_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__8));
v___x_503_ = lean_name_eq(v_kind_492_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__10));
v___x_505_ = lean_name_eq(v_kind_492_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__12));
v___x_507_ = lean_name_eq(v_kind_492_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
lean_dec_ref(v_options_489_);
v___x_508_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__14));
v___x_509_ = lean_name_eq(v_kind_492_, v___x_508_);
lean_dec(v_kind_492_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_stx_486_);
v___x_510_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__16, &l_Lean_Elab_Level_elabLevel___closed__16_once, _init_l_Lean_Elab_Level_elabLevel___closed__16);
v___x_511_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_510_, v___x_496_, v_a_488_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_Syntax_getArg(v_stx_486_, v___x_512_);
lean_inc_ref(v___x_496_);
v___x_514_ = l_Lean_Elab_Level_elabLevel(v___x_513_, v___x_496_, v_a_488_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
v_a_516_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_514_, 2);
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = l_Lean_Syntax_getArg(v_stx_486_, v___x_517_);
lean_dec(v_stx_486_);
v___x_519_ = l_Lean_Syntax_isNatLit_x3f(v___x_518_);
lean_dec(v___x_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; 
lean_dec(v_a_515_);
v___x_520_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_496_, v_a_516_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; 
v_val_521_ = lean_ctor_get(v___x_519_, 0);
lean_inc_n(v_val_521_, 2);
lean_dec_ref_known(v___x_519_, 1);
v___x_522_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_521_, v___x_496_, v_a_516_);
lean_dec_ref_known(v___x_496_, 2);
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
lean_dec_ref_known(v___x_496_, 2);
lean_dec(v_stx_486_);
return v___x_514_;
}
}
}
else
{
lean_object* v_ngen_542_; lean_object* v_mctx_543_; lean_object* v_levelNames_544_; lean_object* v_paramName_545_; lean_object* v___y_547_; uint8_t v___y_551_; uint8_t v___x_580_; 
lean_dec(v_kind_492_);
v_ngen_542_ = lean_ctor_get(v_a_488_, 0);
v_mctx_543_ = lean_ctor_get(v_a_488_, 1);
v_levelNames_544_ = lean_ctor_get(v_a_488_, 2);
v_paramName_545_ = l_Lean_Syntax_getId(v_stx_486_);
lean_dec(v_stx_486_);
v___x_580_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_paramName_545_, v_levelNames_544_);
if (v___x_580_ == 0)
{
if (v_autoBoundImplicit_491_ == 0)
{
lean_dec_ref(v_options_489_);
v___y_551_ = v___x_580_;
goto v___jp_550_;
}
else
{
lean_object* v___x_581_; uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_581_ = l_Lean_Elab_relaxedAutoImplicit;
v___x_582_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_489_, v___x_581_);
lean_dec_ref(v_options_489_);
lean_inc(v_paramName_545_);
v___x_583_ = l_Lean_Elab_isValidAutoBoundLevelName(v_paramName_545_, v___x_582_);
v___y_551_ = v___x_583_;
goto v___jp_550_;
}
}
else
{
lean_dec_ref_known(v___x_496_, 2);
lean_dec_ref(v_options_489_);
v___y_547_ = v_a_488_;
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
if (v___y_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_552_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__18, &l_Lean_Elab_Level_elabLevel___closed__18_once, _init_l_Lean_Elab_Level_elabLevel___closed__18);
lean_inc(v_paramName_545_);
v___x_553_ = l_Lean_mkIdent(v_paramName_545_);
v___x_554_ = l_Lean_MessageData_ofSyntax(v___x_553_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_552_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_557_, v___x_496_, v_a_488_);
lean_dec_ref_known(v___x_496_, 2);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 2);
v___y_547_ = v_a_559_;
goto v___jp_546_;
}
else
{
lean_object* v_a_560_; lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_paramName_545_);
v_a_560_ = lean_ctor_get(v___x_558_, 0);
v_a_561_ = lean_ctor_get(v___x_558_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_558_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_inc(v_a_560_);
lean_dec(v___x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_560_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
lean_inc(v_levelNames_544_);
lean_inc_ref(v_mctx_543_);
lean_inc_ref(v_ngen_542_);
lean_dec_ref_known(v___x_496_, 2);
v_isSharedCheck_576_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_577_ = lean_ctor_get(v_a_488_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_a_488_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_a_488_, 0);
lean_dec(v_unused_579_);
v___x_570_ = v_a_488_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_a_488_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc(v_paramName_545_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_paramName_545_);
lean_ctor_set(v___x_572_, 1, v_levelNames_544_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_mctx_543_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v___y_547_ = v___x_574_;
goto v___jp_546_;
}
}
}
}
}
}
else
{
lean_object* v___x_584_; 
lean_dec(v_kind_492_);
lean_dec_ref(v_options_489_);
v___x_584_ = l_Lean_Syntax_isNatLit_x3f(v_stx_486_);
lean_dec(v_stx_486_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_496_, v_a_488_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_585_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_587_; 
v_val_586_ = lean_ctor_get(v___x_584_, 0);
lean_inc_n(v_val_586_, 2);
lean_dec_ref_known(v___x_584_, 1);
v___x_587_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_586_, v___x_496_, v_a_488_);
lean_dec_ref_known(v___x_496_, 2);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_a_588_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_587_, 0);
lean_dec(v_unused_597_);
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = l_Lean_Level_ofNat(v_val_586_);
lean_dec(v_val_586_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_588_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_val_586_);
v_a_598_ = lean_ctor_get(v___x_587_, 0);
v_a_599_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_587_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_inc(v_a_598_);
lean_dec(v___x_587_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_598_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
else
{
lean_object* v___x_607_; 
lean_dec(v_kind_492_);
lean_dec_ref(v_options_489_);
lean_dec(v_stx_486_);
v___x_607_ = l_Lean_Elab_Level_mkFreshLevelMVar(v___x_496_, v_a_488_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_607_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_args_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_kind_492_);
lean_dec_ref(v_options_489_);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = l_Lean_Syntax_getArg(v_stx_486_, v___x_608_);
lean_dec(v_stx_486_);
v_args_610_ = l_Lean_Syntax_getArgs(v___x_609_);
lean_dec(v___x_609_);
v___x_611_ = lean_array_get_size(v_args_610_);
v___x_612_ = lean_nat_sub(v___x_611_, v___x_608_);
v___x_613_ = lean_array_get(v___x_497_, v_args_610_, v___x_612_);
lean_inc_ref(v___x_496_);
v___x_614_ = l_Lean_Elab_Level_elabLevel(v___x_613_, v___x_496_, v_a_488_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_array_619_; lean_object* v_start_620_; lean_object* v_stop_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Array_toSubarray___redArg(v_args_610_, v___x_617_, v___x_612_);
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
lean_dec_ref_known(v___x_496_, 2);
return v___x_614_;
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
lean_dec_ref_known(v___x_614_, 2);
v___x_625_ = lean_usize_of_nat(v___x_622_);
v___x_626_ = lean_usize_of_nat(v_start_620_);
lean_dec(v_start_620_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_619_, v___x_625_, v___x_626_, v_a_615_, v___x_496_, v_a_616_);
lean_dec_ref_known(v___x_496_, 2);
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
lean_dec_ref_known(v___x_496_, 2);
return v___x_614_;
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
lean_dec_ref_known(v___x_614_, 2);
v___x_629_ = lean_usize_of_nat(v_stop_621_);
lean_dec(v_stop_621_);
v___x_630_ = lean_usize_of_nat(v_start_620_);
lean_dec(v_start_620_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_619_, v___x_629_, v___x_630_, v_a_615_, v___x_496_, v_a_616_);
lean_dec_ref_known(v___x_496_, 2);
lean_dec_ref(v_array_619_);
return v___x_631_;
}
}
}
else
{
lean_dec(v___x_612_);
lean_dec_ref(v_args_610_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_614_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_args_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_kind_492_);
lean_dec_ref(v_options_489_);
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = l_Lean_Syntax_getArg(v_stx_486_, v___x_632_);
lean_dec(v_stx_486_);
v_args_634_ = l_Lean_Syntax_getArgs(v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = lean_array_get_size(v_args_634_);
v___x_636_ = lean_nat_sub(v___x_635_, v___x_632_);
v___x_637_ = lean_array_get(v___x_497_, v_args_634_, v___x_636_);
lean_inc_ref(v___x_496_);
v___x_638_ = l_Lean_Elab_Level_elabLevel(v___x_637_, v___x_496_, v_a_488_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_array_643_; lean_object* v_start_644_; lean_object* v_stop_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_640_);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = l_Array_toSubarray___redArg(v_args_634_, v___x_641_, v___x_636_);
v_array_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_array_643_);
v_start_644_ = lean_ctor_get(v___x_642_, 1);
lean_inc(v_start_644_);
v_stop_645_ = lean_ctor_get(v___x_642_, 2);
lean_inc(v_stop_645_);
lean_dec_ref(v___x_642_);
v___x_646_ = lean_array_get_size(v_array_643_);
v___x_647_ = lean_nat_dec_le(v_stop_645_, v___x_646_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; 
lean_dec(v_stop_645_);
v___x_648_ = lean_nat_dec_lt(v_start_644_, v___x_646_);
if (v___x_648_ == 0)
{
lean_dec(v_start_644_);
lean_dec_ref(v_array_643_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_638_;
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
lean_dec_ref_known(v___x_638_, 2);
v___x_649_ = lean_usize_of_nat(v___x_646_);
v___x_650_ = lean_usize_of_nat(v_start_644_);
lean_dec(v_start_644_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_643_, v___x_649_, v___x_650_, v_a_639_, v___x_496_, v_a_640_);
lean_dec_ref_known(v___x_496_, 2);
lean_dec_ref(v_array_643_);
return v___x_651_;
}
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_lt(v_start_644_, v_stop_645_);
if (v___x_652_ == 0)
{
lean_dec(v_stop_645_);
lean_dec(v_start_644_);
lean_dec_ref(v_array_643_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_638_;
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
lean_dec_ref_known(v___x_638_, 2);
v___x_653_ = lean_usize_of_nat(v_stop_645_);
lean_dec(v_stop_645_);
v___x_654_ = lean_usize_of_nat(v_start_644_);
lean_dec(v_start_644_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_643_, v___x_653_, v___x_654_, v_a_639_, v___x_496_, v_a_640_);
lean_dec_ref_known(v___x_496_, 2);
lean_dec_ref(v_array_643_);
return v___x_655_;
}
}
}
else
{
lean_dec(v___x_636_);
lean_dec_ref(v_args_634_);
lean_dec_ref_known(v___x_496_, 2);
return v___x_638_;
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_kind_492_);
lean_dec_ref(v_options_489_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = l_Lean_Syntax_getArg(v_stx_486_, v___x_656_);
lean_dec(v_stx_486_);
v_stx_486_ = v___x_657_;
v_a_487_ = v___x_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* v_as_659_, size_t v_i_660_, size_t v_stop_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_eq(v_i_660_, v_stop_661_);
if (v___x_665_ == 0)
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_sub(v_i_660_, v___x_666_);
v___x_668_ = lean_array_uget_borrowed(v_as_659_, v___x_667_);
lean_inc_ref(v___y_663_);
lean_inc(v___x_668_);
v___x_669_ = l_Lean_Elab_Level_elabLevel(v___x_668_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
v_a_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_669_, 2);
v___x_672_ = l_Lean_mkLevelIMax_x27(v_a_670_, v_b_662_);
v_i_660_ = v___x_667_;
v_b_662_ = v___x_672_;
v___y_664_ = v_a_671_;
goto _start;
}
else
{
lean_dec(v_b_662_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_674_; lean_object* v_a_675_; 
v_a_674_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_674_);
v_a_675_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_669_, 2);
v_i_660_ = v___x_667_;
v_b_662_ = v_a_674_;
v___y_664_ = v_a_675_;
goto _start;
}
else
{
return v___x_669_;
}
}
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_b_662_);
lean_ctor_set(v___x_677_, 1, v___y_664_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_stop_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_i_boxed_684_; size_t v_stop_boxed_685_; lean_object* v_res_686_; 
v_i_boxed_684_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_stop_boxed_685_ = lean_unbox_usize(v_stop_680_);
lean_dec(v_stop_680_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_678_, v_i_boxed_684_, v_stop_boxed_685_, v_b_681_, v___y_682_, v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v_as_678_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* v_as_687_, lean_object* v_i_688_, lean_object* v_stop_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
size_t v_i_boxed_693_; size_t v_stop_boxed_694_; lean_object* v_res_695_; 
v_i_boxed_693_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_stop_boxed_694_ = lean_unbox_usize(v_stop_689_);
lean_dec(v_stop_689_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_687_, v_i_boxed_693_, v_stop_boxed_694_, v_b_690_, v___y_691_, v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec_ref(v_as_687_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* v_00_u03b1_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_697_, v___y_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* v_00_u03b1_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(v_00_u03b1_700_, v___y_701_, v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_703_;
}
}
lean_object* runtime_initialize_Lean_Elab_AutoBound(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_AutoBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
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
