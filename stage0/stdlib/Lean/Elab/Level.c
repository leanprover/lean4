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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
return v___x_477_;
}
}
else
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_b_470_);
lean_ctor_set(v___x_482_, 1, v___y_472_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* v_stx_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_options_486_; lean_object* v_ref_487_; uint8_t v_autoBoundImplicit_488_; lean_object* v_kind_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v_ref_492_; lean_object* v___x_493_; 
v_options_486_ = lean_ctor_get(v_a_484_, 0);
lean_inc_ref_n(v_options_486_, 2);
v_ref_487_ = lean_ctor_get(v_a_484_, 1);
lean_inc(v_ref_487_);
v_autoBoundImplicit_488_ = lean_ctor_get_uint8(v_a_484_, sizeof(void*)*2);
lean_dec_ref(v_a_484_);
lean_inc(v_stx_483_);
v_kind_489_ = l_Lean_Syntax_getKind(v_stx_483_);
v___x_490_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__2));
v___x_491_ = lean_name_eq(v_kind_489_, v___x_490_);
v_ref_492_ = l_Lean_replaceRef(v_stx_483_, v_ref_487_);
lean_dec(v_ref_487_);
v___x_493_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_493_, 0, v_options_486_);
lean_ctor_set(v___x_493_, 1, v_ref_492_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*2, v_autoBoundImplicit_488_);
if (v___x_491_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_box(0);
v___x_495_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__4));
v___x_496_ = lean_name_eq(v_kind_489_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__6));
v___x_498_ = lean_name_eq(v_kind_489_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__8));
v___x_500_ = lean_name_eq(v_kind_489_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__10));
v___x_502_ = lean_name_eq(v_kind_489_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__12));
v___x_504_ = lean_name_eq(v_kind_489_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
lean_dec_ref(v_options_486_);
v___x_505_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__14));
v___x_506_ = lean_name_eq(v_kind_489_, v___x_505_);
lean_dec(v_kind_489_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_stx_483_);
v___x_507_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__16, &l_Lean_Elab_Level_elabLevel___closed__16_once, _init_l_Lean_Elab_Level_elabLevel___closed__16);
v___x_508_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_507_, v___x_493_, v_a_485_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l_Lean_Syntax_getArg(v_stx_483_, v___x_509_);
lean_inc_ref(v___x_493_);
v___x_511_ = l_Lean_Elab_Level_elabLevel(v___x_510_, v___x_493_, v_a_485_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v_a_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
v_a_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_511_, 2);
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = l_Lean_Syntax_getArg(v_stx_483_, v___x_514_);
lean_dec(v_stx_483_);
v___x_516_ = l_Lean_Syntax_isNatLit_x3f(v___x_515_);
lean_dec(v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; 
lean_dec(v_a_512_);
v___x_517_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_493_, v_a_513_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_517_;
}
else
{
lean_object* v_val_518_; lean_object* v___x_519_; 
v_val_518_ = lean_ctor_get(v___x_516_, 0);
lean_inc_n(v_val_518_, 2);
lean_dec_ref_known(v___x_516_, 1);
v___x_519_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_518_, v___x_493_, v_a_513_);
lean_dec_ref_known(v___x_493_, 2);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_a_520_ = lean_ctor_get(v___x_519_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_529_);
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Lean_Level_addOffset(v_a_512_, v_val_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_val_518_);
lean_dec(v_a_512_);
v_a_530_ = lean_ctor_get(v___x_519_, 0);
v_a_531_ = lean_ctor_get(v___x_519_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_519_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_inc(v_a_530_);
lean_dec(v___x_519_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_493_, 2);
lean_dec(v_stx_483_);
return v___x_511_;
}
}
}
else
{
lean_object* v_ngen_539_; lean_object* v_mctx_540_; lean_object* v_levelNames_541_; lean_object* v_paramName_542_; lean_object* v___y_544_; uint8_t v___x_565_; 
lean_dec(v_kind_489_);
v_ngen_539_ = lean_ctor_get(v_a_485_, 0);
v_mctx_540_ = lean_ctor_get(v_a_485_, 1);
v_levelNames_541_ = lean_ctor_get(v_a_485_, 2);
v_paramName_542_ = l_Lean_Syntax_getId(v_stx_483_);
lean_dec(v_stx_483_);
v___x_565_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_paramName_542_, v_levelNames_541_);
if (v___x_565_ == 0)
{
if (v_autoBoundImplicit_488_ == 0)
{
lean_dec_ref(v_options_486_);
goto v___jp_547_;
}
else
{
lean_object* v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_Elab_relaxedAutoImplicit;
v___x_567_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_486_, v___x_566_);
lean_dec_ref(v_options_486_);
lean_inc(v_paramName_542_);
v___x_568_ = l_Lean_Elab_isValidAutoBoundLevelName(v_paramName_542_, v___x_567_);
if (v___x_568_ == 0)
{
goto v___jp_547_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
lean_inc(v_levelNames_541_);
lean_inc_ref(v_mctx_540_);
lean_inc_ref(v_ngen_539_);
lean_dec_ref_known(v___x_493_, 2);
v_isSharedCheck_576_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_577_ = lean_ctor_get(v_a_485_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_a_485_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_a_485_, 0);
lean_dec(v_unused_579_);
v___x_570_ = v_a_485_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_a_485_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
lean_inc(v_paramName_542_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_paramName_542_);
lean_ctor_set(v___x_572_, 1, v_levelNames_541_);
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
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_ngen_539_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_mctx_540_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v___y_544_ = v___x_574_;
goto v___jp_543_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_493_, 2);
lean_dec_ref(v_options_486_);
v___y_544_ = v_a_485_;
goto v___jp_543_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = l_Lean_mkLevelParam(v_paramName_542_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___y_544_);
return v___x_546_;
}
v___jp_547_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__18, &l_Lean_Elab_Level_elabLevel___closed__18_once, _init_l_Lean_Elab_Level_elabLevel___closed__18);
lean_inc(v_paramName_542_);
v___x_549_ = l_Lean_mkIdent(v_paramName_542_);
v___x_550_ = l_Lean_MessageData_ofSyntax(v___x_549_);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_548_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_553_, v___x_493_, v_a_485_);
lean_dec_ref_known(v___x_493_, 2);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v___x_554_, 1);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 2);
v___y_544_ = v_a_555_;
goto v___jp_543_;
}
else
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_paramName_542_);
v_a_556_ = lean_ctor_get(v___x_554_, 0);
v_a_557_ = lean_ctor_get(v___x_554_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_554_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_inc(v_a_556_);
lean_dec(v___x_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_556_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
else
{
lean_object* v___x_580_; 
lean_dec(v_kind_489_);
lean_dec_ref(v_options_486_);
v___x_580_ = l_Lean_Syntax_isNatLit_x3f(v_stx_483_);
lean_dec(v_stx_483_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_493_, v_a_485_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_581_;
}
else
{
lean_object* v_val_582_; lean_object* v___x_583_; 
v_val_582_ = lean_ctor_get(v___x_580_, 0);
lean_inc_n(v_val_582_, 2);
lean_dec_ref_known(v___x_580_, 1);
v___x_583_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_582_, v___x_493_, v_a_485_);
lean_dec_ref_known(v___x_493_, 2);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_a_584_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_593_);
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = l_Lean_Level_ofNat(v_val_582_);
lean_dec(v_val_582_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_a_584_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_val_582_);
v_a_594_ = lean_ctor_get(v___x_583_, 0);
v_a_595_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_583_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_inc(v_a_594_);
lean_dec(v___x_583_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v_kind_489_);
lean_dec_ref(v_options_486_);
lean_dec(v_stx_483_);
v___x_603_ = l_Lean_Elab_Level_mkFreshLevelMVar(v___x_493_, v_a_485_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_args_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_kind_489_);
lean_dec_ref(v_options_486_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = l_Lean_Syntax_getArg(v_stx_483_, v___x_604_);
lean_dec(v_stx_483_);
v_args_606_ = l_Lean_Syntax_getArgs(v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = lean_array_get_size(v_args_606_);
v___x_608_ = lean_nat_sub(v___x_607_, v___x_604_);
v___x_609_ = lean_array_get_borrowed(v___x_494_, v_args_606_, v___x_608_);
lean_inc_ref(v___x_493_);
lean_inc(v___x_609_);
v___x_610_ = l_Lean_Elab_Level_elabLevel(v___x_609_, v___x_493_, v_a_485_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_array_615_; lean_object* v_start_616_; lean_object* v_stop_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_a_612_ = lean_ctor_get(v___x_610_, 1);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = l_Array_toSubarray___redArg(v_args_606_, v___x_613_, v___x_608_);
v_array_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_array_615_);
v_start_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_start_616_);
v_stop_617_ = lean_ctor_get(v___x_614_, 2);
lean_inc(v_stop_617_);
lean_dec_ref(v___x_614_);
v___x_618_ = lean_array_get_size(v_array_615_);
v___x_619_ = lean_nat_dec_le(v_stop_617_, v___x_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
lean_dec(v_stop_617_);
v___x_620_ = lean_nat_dec_lt(v_start_616_, v___x_618_);
if (v___x_620_ == 0)
{
lean_dec(v_start_616_);
lean_dec_ref(v_array_615_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_610_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
lean_inc(v_a_612_);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 2);
v___x_621_ = lean_usize_of_nat(v___x_618_);
v___x_622_ = lean_usize_of_nat(v_start_616_);
lean_dec(v_start_616_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_615_, v___x_621_, v___x_622_, v_a_611_, v___x_493_, v_a_612_);
lean_dec_ref_known(v___x_493_, 2);
lean_dec_ref(v_array_615_);
return v___x_623_;
}
}
else
{
uint8_t v___x_624_; 
v___x_624_ = lean_nat_dec_lt(v_start_616_, v_stop_617_);
if (v___x_624_ == 0)
{
lean_dec(v_stop_617_);
lean_dec(v_start_616_);
lean_dec_ref(v_array_615_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_610_;
}
else
{
size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
lean_inc(v_a_612_);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 2);
v___x_625_ = lean_usize_of_nat(v_stop_617_);
lean_dec(v_stop_617_);
v___x_626_ = lean_usize_of_nat(v_start_616_);
lean_dec(v_start_616_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_615_, v___x_625_, v___x_626_, v_a_611_, v___x_493_, v_a_612_);
lean_dec_ref_known(v___x_493_, 2);
lean_dec_ref(v_array_615_);
return v___x_627_;
}
}
}
else
{
lean_dec(v___x_608_);
lean_dec_ref(v_args_606_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_610_;
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_args_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_kind_489_);
lean_dec_ref(v_options_486_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = l_Lean_Syntax_getArg(v_stx_483_, v___x_628_);
lean_dec(v_stx_483_);
v_args_630_ = l_Lean_Syntax_getArgs(v___x_629_);
lean_dec(v___x_629_);
v___x_631_ = lean_array_get_size(v_args_630_);
v___x_632_ = lean_nat_sub(v___x_631_, v___x_628_);
v___x_633_ = lean_array_get_borrowed(v___x_494_, v_args_630_, v___x_632_);
lean_inc_ref(v___x_493_);
lean_inc(v___x_633_);
v___x_634_ = l_Lean_Elab_Level_elabLevel(v___x_633_, v___x_493_, v_a_485_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_array_639_; lean_object* v_start_640_; lean_object* v_stop_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_a_636_ = lean_ctor_get(v___x_634_, 1);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_Array_toSubarray___redArg(v_args_630_, v___x_637_, v___x_632_);
v_array_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_array_639_);
v_start_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_start_640_);
v_stop_641_ = lean_ctor_get(v___x_638_, 2);
lean_inc(v_stop_641_);
lean_dec_ref(v___x_638_);
v___x_642_ = lean_array_get_size(v_array_639_);
v___x_643_ = lean_nat_dec_le(v_stop_641_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
lean_dec(v_stop_641_);
v___x_644_ = lean_nat_dec_lt(v_start_640_, v___x_642_);
if (v___x_644_ == 0)
{
lean_dec(v_start_640_);
lean_dec_ref(v_array_639_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_634_;
}
else
{
size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; 
lean_inc(v_a_636_);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 2);
v___x_645_ = lean_usize_of_nat(v___x_642_);
v___x_646_ = lean_usize_of_nat(v_start_640_);
lean_dec(v_start_640_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_639_, v___x_645_, v___x_646_, v_a_635_, v___x_493_, v_a_636_);
lean_dec_ref_known(v___x_493_, 2);
lean_dec_ref(v_array_639_);
return v___x_647_;
}
}
else
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_lt(v_start_640_, v_stop_641_);
if (v___x_648_ == 0)
{
lean_dec(v_stop_641_);
lean_dec(v_start_640_);
lean_dec_ref(v_array_639_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_634_;
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
lean_inc(v_a_636_);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 2);
v___x_649_ = lean_usize_of_nat(v_stop_641_);
lean_dec(v_stop_641_);
v___x_650_ = lean_usize_of_nat(v_start_640_);
lean_dec(v_start_640_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_639_, v___x_649_, v___x_650_, v_a_635_, v___x_493_, v_a_636_);
lean_dec_ref_known(v___x_493_, 2);
lean_dec_ref(v_array_639_);
return v___x_651_;
}
}
}
else
{
lean_dec(v___x_632_);
lean_dec_ref(v_args_630_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_634_;
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_kind_489_);
lean_dec_ref(v_options_486_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = l_Lean_Syntax_getArg(v_stx_483_, v___x_652_);
lean_dec(v_stx_483_);
v_stx_483_ = v___x_653_;
v_a_484_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* v_as_655_, size_t v_i_656_, size_t v_stop_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_eq(v_i_656_, v_stop_657_);
if (v___x_661_ == 0)
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v_i_656_, v___x_662_);
v___x_664_ = lean_array_uget_borrowed(v_as_655_, v___x_663_);
lean_inc_ref(v___y_659_);
lean_inc(v___x_664_);
v___x_665_ = l_Lean_Elab_Level_elabLevel(v___x_664_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
v_a_667_ = lean_ctor_get(v___x_665_, 1);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_665_, 2);
v___x_668_ = l_Lean_mkLevelIMax_x27(v_a_666_, v_b_658_);
v_i_656_ = v___x_663_;
v_b_658_ = v___x_668_;
v___y_660_ = v_a_667_;
goto _start;
}
else
{
lean_dec(v_b_658_);
return v___x_665_;
}
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_b_658_);
lean_ctor_set(v___x_670_, 1, v___y_660_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* v_as_671_, lean_object* v_i_672_, lean_object* v_stop_673_, lean_object* v_b_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
size_t v_i_boxed_677_; size_t v_stop_boxed_678_; lean_object* v_res_679_; 
v_i_boxed_677_ = lean_unbox_usize(v_i_672_);
lean_dec(v_i_672_);
v_stop_boxed_678_ = lean_unbox_usize(v_stop_673_);
lean_dec(v_stop_673_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_671_, v_i_boxed_677_, v_stop_boxed_678_, v_b_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v_as_671_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* v_as_680_, lean_object* v_i_681_, lean_object* v_stop_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
size_t v_i_boxed_686_; size_t v_stop_boxed_687_; lean_object* v_res_688_; 
v_i_boxed_686_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_stop_boxed_687_ = lean_unbox_usize(v_stop_682_);
lean_dec(v_stop_682_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_680_, v_i_boxed_686_, v_stop_boxed_687_, v_b_683_, v___y_684_, v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v_as_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* v_00_u03b1_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_690_, v___y_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* v_00_u03b1_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(v_00_u03b1_693_, v___y_694_, v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_696_;
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
