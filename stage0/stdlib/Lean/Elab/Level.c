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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* v_name_209_, lean_object* v_decl_210_, lean_object* v_ref_211_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_209_ = stack[0].m_obj;
lean_object* v_decl_210_ = stack[1].m_obj;
lean_object* v_ref_211_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_209_, v_decl_210_, v_ref_211_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_237_, lean_object* v_decl_238_, lean_object* v_ref_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_237_, v_decl_238_, v_ref_239_);
lean_dec_ref(v_decl_238_);
return v_res_241_;
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_261_ = ((lean_object*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_));
v___x_262_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v___x_259_, v___x_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_263_;
v_res_263_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object* v___x_280_, lean_object* v_n_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_toPure_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v___x_286_; lean_object* v_max_287_; uint8_t v___x_288_; 
v___x_286_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_287_ = l_Lean_Option_get___redArg(v___x_280_, v_____do__lift_285_, v___x_286_);
v___x_288_ = lean_nat_dec_le(v_n_281_, v_max_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_toPure_284_);
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
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_max_287_);
lean_dec_ref(v_inst_283_);
lean_dec_ref(v_inst_282_);
lean_dec(v_n_281_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* v___x_307_, lean_object* v_n_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_toPure_311_, lean_object* v_____do__lift_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(v___x_307_, v_n_308_, v_inst_309_, v_inst_310_, v_toPure_311_, v_____do__lift_312_);
lean_dec_ref(v_____do__lift_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_n_317_){
_start:
{
lean_object* v___x_318_; lean_object* v_toApplicative_319_; lean_object* v_toBind_320_; lean_object* v_getOptions_321_; lean_object* v_toPure_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
v___x_318_ = l_Lean_KVMap_instValueNat;
v_toApplicative_319_ = lean_ctor_get(v_inst_314_, 0);
v_toBind_320_ = lean_ctor_get(v_inst_314_, 1);
lean_inc(v_toBind_320_);
v_getOptions_321_ = lean_ctor_get(v_inst_316_, 0);
lean_inc(v_getOptions_321_);
lean_dec_ref(v_inst_316_);
v_toPure_322_ = lean_ctor_get(v_toApplicative_319_, 1);
lean_inc(v_toPure_322_);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_323_, 0, v___x_318_);
lean_closure_set(v___f_323_, 1, v_n_317_);
lean_closure_set(v___f_323_, 2, v_inst_314_);
lean_closure_set(v___f_323_, 3, v_inst_315_);
lean_closure_set(v___f_323_, 4, v_toPure_322_);
v___x_324_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v_getOptions_321_, v___f_323_);
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
uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object* v_opts_351_, lean_object* v_opt_352_){
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
lean_dec_ref_known(v___x_356_, 1);
if (lean_obj_tag(v_val_358_) == 1)
{
uint8_t v_v_359_; 
v_v_359_ = lean_ctor_get_uint8(v_val_358_, 0);
lean_dec_ref_known(v_val_358_, 0);
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_351_ = stack[0].m_obj;
lean_object* v_opt_352_ = stack[1].m_obj;
uint8_t v_res_361_;
v_res_361_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_351_, v_opt_352_);
stack->m_num = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* v_opts_362_, lean_object* v_opt_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_362_, v_opt_363_);
lean_dec_ref(v_opt_363_);
lean_dec_ref(v_opts_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
v___x_372_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_371_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_373_, v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_375_;
}
}
uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 0;
return v___x_378_;
}
else
{
lean_object* v_head_379_; lean_object* v_tail_380_; uint8_t v___x_381_; 
v_head_379_ = lean_ctor_get(v_x_377_, 0);
v_tail_380_ = lean_ctor_get(v_x_377_, 1);
v___x_381_ = lean_name_eq(v_a_376_, v_head_379_);
if (v___x_381_ == 0)
{
v_x_377_ = v_tail_380_;
goto _start;
}
else
{
return v___x_381_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_376_ = stack[0].m_obj;
lean_object* v_x_377_ = stack[1].m_obj;
uint8_t v_res_383_;
v_res_383_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_376_, v_x_377_);
stack->m_num = v_res_383_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object* v_a_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_384_, v_x_385_);
lean_dec(v_x_385_);
lean_dec(v_a_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* v_opts_388_, lean_object* v_opt_389_){
_start:
{
lean_object* v_name_390_; lean_object* v_defValue_391_; lean_object* v_map_392_; lean_object* v___x_393_; 
v_name_390_ = lean_ctor_get(v_opt_389_, 0);
v_defValue_391_ = lean_ctor_get(v_opt_389_, 1);
v_map_392_ = lean_ctor_get(v_opts_388_, 0);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_392_, v_name_390_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_inc(v_defValue_391_);
return v_defValue_391_;
}
else
{
lean_object* v_val_394_; 
v_val_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_393_, 1);
if (lean_obj_tag(v_val_394_) == 3)
{
lean_object* v_v_395_; 
v_v_395_ = lean_ctor_get(v_val_394_, 0);
lean_inc(v_v_395_);
lean_dec_ref_known(v_val_394_, 1);
return v_v_395_;
}
else
{
lean_dec(v_val_394_);
lean_inc(v_defValue_391_);
return v_defValue_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* v_opts_396_, lean_object* v_opt_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_opts_396_, v_opt_397_);
lean_dec_ref(v_opt_397_);
lean_dec_ref(v_opts_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object* v_n_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_options_402_; lean_object* v___x_403_; lean_object* v_max_404_; uint8_t v___x_405_; 
v_options_402_ = lean_ctor_get(v___y_400_, 0);
v___x_403_ = l_Lean_Elab_Level_maxUniverseOffset;
v_max_404_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_options_402_, v___x_403_);
v___x_405_ = lean_nat_dec_le(v_n_399_, v_max_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
v___x_407_ = l_Nat_reprFast(v_n_399_);
v___x_408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = l_Lean_MessageData_ofFormat(v___x_408_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_406_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Nat_reprFast(v_max_404_);
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___x_415_ = l_Lean_MessageData_ofFormat(v___x_414_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_412_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
v___x_420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_420_, v___y_400_, v___y_401_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec(v_max_404_);
lean_dec(v_n_399_);
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___y_401_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* v_n_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_n_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_427_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__15));
v___x_467_ = l_Lean_stringToMessageData(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__17));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object* v_as_471_, size_t v_i_472_, size_t v_stop_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_eq(v_i_472_, v_stop_473_);
if (v___x_477_ == 0)
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_sub(v_i_472_, v___x_478_);
v___x_480_ = lean_array_uget_borrowed(v_as_471_, v___x_479_);
lean_inc_ref(v___y_475_);
lean_inc(v___x_480_);
v___x_481_ = l_Lean_Elab_Level_elabLevel(v___x_480_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
v_a_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_481_, 2);
v___x_484_ = l_Lean_mkLevelMax_x27(v_a_482_, v_b_474_);
v_i_472_ = v___x_479_;
v_b_474_ = v___x_484_;
v___y_476_ = v_a_483_;
goto _start;
}
else
{
lean_dec(v_b_474_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_486_; lean_object* v_a_487_; 
v_a_486_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_486_);
v_a_487_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_481_, 2);
v_i_472_ = v___x_479_;
v_b_474_ = v_a_486_;
v___y_476_ = v_a_487_;
goto _start;
}
else
{
return v___x_481_;
}
}
}
else
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_b_474_);
lean_ctor_set(v___x_489_, 1, v___y_476_);
return v___x_489_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_471_ = stack[0].m_obj;
size_t v_i_472_ = stack[1].m_num;
size_t v_stop_473_ = stack[2].m_num;
lean_object* v_b_474_ = stack[3].m_obj;
lean_object* v___y_475_ = stack[4].m_obj;
lean_object* v___y_476_ = stack[5].m_obj;
lean_object* v_res_490_;
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_471_, v_i_472_, v_stop_473_, v_b_474_, v___y_475_, v___y_476_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* v_stx_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_options_494_; lean_object* v_ref_495_; uint8_t v_autoBoundImplicit_496_; lean_object* v_kind_497_; lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v_ref_500_; lean_object* v___x_501_; 
v_options_494_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref_n(v_options_494_, 2);
v_ref_495_ = lean_ctor_get(v_a_492_, 1);
lean_inc(v_ref_495_);
v_autoBoundImplicit_496_ = lean_ctor_get_uint8(v_a_492_, sizeof(void*)*2);
lean_dec_ref(v_a_492_);
lean_inc(v_stx_491_);
v_kind_497_ = l_Lean_Syntax_getKind(v_stx_491_);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__2));
v___x_499_ = lean_name_eq(v_kind_497_, v___x_498_);
v_ref_500_ = l_Lean_replaceRef(v_stx_491_, v_ref_495_);
lean_dec(v_ref_495_);
v___x_501_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_501_, 0, v_options_494_);
lean_ctor_set(v___x_501_, 1, v_ref_500_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*2, v_autoBoundImplicit_496_);
if (v___x_499_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_box(0);
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
lean_dec_ref(v_options_494_);
v___x_513_ = ((lean_object*)(l_Lean_Elab_Level_elabLevel___closed__14));
v___x_514_ = lean_name_eq(v_kind_497_, v___x_513_);
lean_dec(v_kind_497_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_stx_491_);
v___x_515_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__16, &l_Lean_Elab_Level_elabLevel___closed__16_once, _init_l_Lean_Elab_Level_elabLevel___closed__16);
v___x_516_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_515_, v___x_501_, v_a_493_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_Syntax_getArg(v_stx_491_, v___x_517_);
lean_inc_ref(v___x_501_);
v___x_519_ = l_Lean_Elab_Level_elabLevel(v___x_518_, v___x_501_, v_a_493_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
v_a_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_519_, 2);
v___x_522_ = lean_unsigned_to_nat(2u);
v___x_523_ = l_Lean_Syntax_getArg(v_stx_491_, v___x_522_);
lean_dec(v_stx_491_);
v___x_524_ = l_Lean_Syntax_isNatLit_x3f(v___x_523_);
lean_dec(v___x_523_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_525_; 
lean_dec(v_a_520_);
v___x_525_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_501_, v_a_521_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_525_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
v_val_526_ = lean_ctor_get(v___x_524_, 0);
lean_inc_n(v_val_526_, 2);
lean_dec_ref_known(v___x_524_, 1);
v___x_527_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_526_, v___x_501_, v_a_521_);
lean_dec_ref_known(v___x_501_, 2);
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
lean_dec_ref_known(v___x_501_, 2);
lean_dec(v_stx_491_);
return v___x_519_;
}
}
}
else
{
lean_object* v_ngen_547_; lean_object* v_mctx_548_; lean_object* v_levelNames_549_; lean_object* v_paramName_550_; lean_object* v___y_552_; uint8_t v___y_556_; uint8_t v___x_585_; 
lean_dec(v_kind_497_);
v_ngen_547_ = lean_ctor_get(v_a_493_, 0);
v_mctx_548_ = lean_ctor_get(v_a_493_, 1);
v_levelNames_549_ = lean_ctor_get(v_a_493_, 2);
v_paramName_550_ = l_Lean_Syntax_getId(v_stx_491_);
lean_dec(v_stx_491_);
v___x_585_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_paramName_550_, v_levelNames_549_);
if (v___x_585_ == 0)
{
if (v_autoBoundImplicit_496_ == 0)
{
lean_dec_ref(v_options_494_);
v___y_556_ = v___x_585_;
goto v___jp_555_;
}
else
{
lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_586_ = l_Lean_Elab_relaxedAutoImplicit;
v___x_587_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_494_, v___x_586_);
lean_dec_ref(v_options_494_);
lean_inc(v_paramName_550_);
v___x_588_ = l_Lean_Elab_isValidAutoBoundLevelName(v_paramName_550_, v___x_587_);
v___y_556_ = v___x_588_;
goto v___jp_555_;
}
}
else
{
lean_dec_ref_known(v___x_501_, 2);
lean_dec_ref(v_options_494_);
v___y_552_ = v_a_493_;
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
if (v___y_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_557_ = lean_obj_once(&l_Lean_Elab_Level_elabLevel___closed__18, &l_Lean_Elab_Level_elabLevel___closed__18_once, _init_l_Lean_Elab_Level_elabLevel___closed__18);
lean_inc(v_paramName_550_);
v___x_558_ = l_Lean_mkIdent(v_paramName_550_);
v___x_559_ = l_Lean_MessageData_ofSyntax(v___x_558_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_obj_once(&l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5, &l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_562_, v___x_501_, v_a_493_);
lean_dec_ref_known(v___x_501_, 2);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; 
v_a_564_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 2);
v___y_552_ = v_a_564_;
goto v___jp_551_;
}
else
{
lean_object* v_a_565_; lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_paramName_550_);
v_a_565_ = lean_ctor_get(v___x_563_, 0);
v_a_566_ = lean_ctor_get(v___x_563_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_563_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_inc(v_a_565_);
lean_dec(v___x_563_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_565_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_581_; 
lean_inc(v_levelNames_549_);
lean_inc_ref(v_mctx_548_);
lean_inc_ref(v_ngen_547_);
lean_dec_ref_known(v___x_501_, 2);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; 
v_unused_582_ = lean_ctor_get(v_a_493_, 2);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_a_493_, 1);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_a_493_, 0);
lean_dec(v_unused_584_);
v___x_575_ = v_a_493_;
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_a_493_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
lean_inc(v_paramName_550_);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v_paramName_550_);
lean_ctor_set(v___x_577_, 1, v_levelNames_549_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 2, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_mctx_548_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
v___y_552_ = v___x_579_;
goto v___jp_551_;
}
}
}
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_494_);
v___x_589_ = l_Lean_Syntax_isNatLit_x3f(v_stx_491_);
lean_dec(v_stx_491_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_501_, v_a_493_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_592_; 
v_val_591_ = lean_ctor_get(v___x_589_, 0);
lean_inc_n(v_val_591_, 2);
lean_dec_ref_known(v___x_589_, 1);
v___x_592_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_591_, v___x_501_, v_a_493_);
lean_dec_ref_known(v___x_501_, 2);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_a_593_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_602_);
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = l_Lean_Level_ofNat(v_val_591_);
lean_dec(v_val_591_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_593_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_val_591_);
v_a_603_ = lean_ctor_get(v___x_592_, 0);
v_a_604_ = lean_ctor_get(v___x_592_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_592_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_inc(v_a_603_);
lean_dec(v___x_592_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_494_);
lean_dec(v_stx_491_);
v___x_612_ = l_Lean_Elab_Level_mkFreshLevelMVar(v___x_501_, v_a_493_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_612_;
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_args_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_494_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = l_Lean_Syntax_getArg(v_stx_491_, v___x_613_);
lean_dec(v_stx_491_);
v_args_615_ = l_Lean_Syntax_getArgs(v___x_614_);
lean_dec(v___x_614_);
v___x_616_ = lean_array_get_size(v_args_615_);
v___x_617_ = lean_nat_sub(v___x_616_, v___x_613_);
v___x_618_ = lean_array_get_borrowed(v___x_502_, v_args_615_, v___x_617_);
lean_inc_ref(v___x_501_);
lean_inc(v___x_618_);
v___x_619_ = l_Lean_Elab_Level_elabLevel(v___x_618_, v___x_501_, v_a_493_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_array_624_; lean_object* v_start_625_; lean_object* v_stop_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_a_621_ = lean_ctor_get(v___x_619_, 1);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_Array_toSubarray___redArg(v_args_615_, v___x_622_, v___x_617_);
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
lean_dec_ref_known(v___x_501_, 2);
return v___x_619_;
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 2);
v___x_630_ = lean_usize_of_nat(v___x_627_);
v___x_631_ = lean_usize_of_nat(v_start_625_);
lean_dec(v_start_625_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_624_, v___x_630_, v___x_631_, v_a_620_, v___x_501_, v_a_621_);
lean_dec_ref_known(v___x_501_, 2);
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
lean_dec_ref_known(v___x_501_, 2);
return v___x_619_;
}
else
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 2);
v___x_634_ = lean_usize_of_nat(v_stop_626_);
lean_dec(v_stop_626_);
v___x_635_ = lean_usize_of_nat(v_start_625_);
lean_dec(v_start_625_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_624_, v___x_634_, v___x_635_, v_a_620_, v___x_501_, v_a_621_);
lean_dec_ref_known(v___x_501_, 2);
lean_dec_ref(v_array_624_);
return v___x_636_;
}
}
}
else
{
lean_dec(v___x_617_);
lean_dec_ref(v_args_615_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_619_;
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_args_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_494_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = l_Lean_Syntax_getArg(v_stx_491_, v___x_637_);
lean_dec(v_stx_491_);
v_args_639_ = l_Lean_Syntax_getArgs(v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = lean_array_get_size(v_args_639_);
v___x_641_ = lean_nat_sub(v___x_640_, v___x_637_);
v___x_642_ = lean_array_get_borrowed(v___x_502_, v_args_639_, v___x_641_);
lean_inc_ref(v___x_501_);
lean_inc(v___x_642_);
v___x_643_ = l_Lean_Elab_Level_elabLevel(v___x_642_, v___x_501_, v_a_493_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_array_648_; lean_object* v_start_649_; lean_object* v_stop_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_a_645_ = lean_ctor_get(v___x_643_, 1);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_Array_toSubarray___redArg(v_args_639_, v___x_646_, v___x_641_);
v_array_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_array_648_);
v_start_649_ = lean_ctor_get(v___x_647_, 1);
lean_inc(v_start_649_);
v_stop_650_ = lean_ctor_get(v___x_647_, 2);
lean_inc(v_stop_650_);
lean_dec_ref(v___x_647_);
v___x_651_ = lean_array_get_size(v_array_648_);
v___x_652_ = lean_nat_dec_le(v_stop_650_, v___x_651_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
lean_dec(v_stop_650_);
v___x_653_ = lean_nat_dec_lt(v_start_649_, v___x_651_);
if (v___x_653_ == 0)
{
lean_dec(v_start_649_);
lean_dec_ref(v_array_648_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_643_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
lean_inc(v_a_645_);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 2);
v___x_654_ = lean_usize_of_nat(v___x_651_);
v___x_655_ = lean_usize_of_nat(v_start_649_);
lean_dec(v_start_649_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_648_, v___x_654_, v___x_655_, v_a_644_, v___x_501_, v_a_645_);
lean_dec_ref_known(v___x_501_, 2);
lean_dec_ref(v_array_648_);
return v___x_656_;
}
}
else
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_lt(v_start_649_, v_stop_650_);
if (v___x_657_ == 0)
{
lean_dec(v_stop_650_);
lean_dec(v_start_649_);
lean_dec_ref(v_array_648_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_643_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
lean_inc(v_a_645_);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 2);
v___x_658_ = lean_usize_of_nat(v_stop_650_);
lean_dec(v_stop_650_);
v___x_659_ = lean_usize_of_nat(v_start_649_);
lean_dec(v_start_649_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_648_, v___x_658_, v___x_659_, v_a_644_, v___x_501_, v_a_645_);
lean_dec_ref_known(v___x_501_, 2);
lean_dec_ref(v_array_648_);
return v___x_660_;
}
}
}
else
{
lean_dec(v___x_641_);
lean_dec_ref(v_args_639_);
lean_dec_ref_known(v___x_501_, 2);
return v___x_643_;
}
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_kind_497_);
lean_dec_ref(v_options_494_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = l_Lean_Syntax_getArg(v_stx_491_, v___x_661_);
lean_dec(v_stx_491_);
v_stx_491_ = v___x_662_;
v_a_492_ = v___x_501_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* v_as_664_, size_t v_i_665_, size_t v_stop_666_, lean_object* v_b_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_usize_dec_eq(v_i_665_, v_stop_666_);
if (v___x_670_ == 0)
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_sub(v_i_665_, v___x_671_);
v___x_673_ = lean_array_uget_borrowed(v_as_664_, v___x_672_);
lean_inc_ref(v___y_668_);
lean_inc(v___x_673_);
v___x_674_ = l_Lean_Elab_Level_elabLevel(v___x_673_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
v_a_676_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_674_, 2);
v___x_677_ = l_Lean_mkLevelIMax_x27(v_a_675_, v_b_667_);
v_i_665_ = v___x_672_;
v_b_667_ = v___x_677_;
v___y_669_ = v_a_676_;
goto _start;
}
else
{
lean_dec(v_b_667_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_679_; lean_object* v_a_680_; 
v_a_679_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_679_);
v_a_680_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_674_, 2);
v_i_665_ = v___x_672_;
v_b_667_ = v_a_679_;
v___y_669_ = v_a_680_;
goto _start;
}
else
{
return v___x_674_;
}
}
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_b_667_);
lean_ctor_set(v___x_682_, 1, v___y_669_);
return v___x_682_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_664_ = stack[0].m_obj;
size_t v_i_665_ = stack[1].m_num;
size_t v_stop_666_ = stack[2].m_num;
lean_object* v_b_667_ = stack[3].m_obj;
lean_object* v___y_668_ = stack[4].m_obj;
lean_object* v___y_669_ = stack[5].m_obj;
lean_object* v_res_683_;
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_664_, v_i_665_, v_stop_666_, v_b_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* v_as_684_, lean_object* v_i_685_, lean_object* v_stop_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v_i_boxed_690_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_686_);
lean_dec(v_stop_686_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_684_, v_i_boxed_690_, v_stop_boxed_691_, v_b_687_, v___y_688_, v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_as_684_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_i_boxed_699_; size_t v_stop_boxed_700_; lean_object* v_res_701_; 
v_i_boxed_699_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_700_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_693_, v_i_boxed_699_, v_stop_boxed_700_, v_b_696_, v___y_697_, v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v_as_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* v_00_u03b1_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___y_703_, v___y_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* v_00_u03b1_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(v_00_u03b1_706_, v___y_707_, v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_709_;
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
