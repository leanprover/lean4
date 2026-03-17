// Lean compiler output
// Module: Init.System.ST
// Imports: public import Init.Control.Except public import Init.NotationExtra import Init.Classical
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
LEAN_EXPORT lean_object* l_Void_nonemptyType(lean_object*);
lean_object* lean_void_mk(lean_object*);
LEAN_EXPORT lean_object* l_Void_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ST_pure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_bind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadST___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__0 = (const lean_object*)&l_instMonadST___closed__0_value;
static const lean_closure_object l_instMonadST___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__1 = (const lean_object*)&l_instMonadST___closed__1_value;
static const lean_closure_object l_instMonadST___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__2 = (const lean_object*)&l_instMonadST___closed__2_value;
static const lean_closure_object l_instMonadST___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__3 = (const lean_object*)&l_instMonadST___closed__3_value;
static const lean_closure_object l_instMonadST___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__4___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__4 = (const lean_object*)&l_instMonadST___closed__4_value;
static const lean_closure_object l_instMonadST___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__5___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadST___closed__5 = (const lean_object*)&l_instMonadST___closed__5_value;
static const lean_ctor_object l_instMonadST___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadST___closed__0_value),((lean_object*)&l_instMonadST___closed__1_value)}};
static const lean_object* l_instMonadST___closed__6 = (const lean_object*)&l_instMonadST___closed__6_value;
static const lean_ctor_object l_instMonadST___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadST___closed__6_value),((lean_object*)&l_instMonadST___closed__2_value),((lean_object*)&l_instMonadST___closed__3_value),((lean_object*)&l_instMonadST___closed__4_value),((lean_object*)&l_instMonadST___closed__5_value)}};
static const lean_object* l_instMonadST___closed__7 = (const lean_object*)&l_instMonadST___closed__7_value;
static const lean_closure_object l_instMonadST___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ST_bind___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadST___closed__8 = (const lean_object*)&l_instMonadST___closed__8_value;
static const lean_ctor_object l_instMonadST___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadST___closed__7_value),((lean_object*)&l_instMonadST___closed__8_value)}};
static const lean_object* l_instMonadST___closed__9 = (const lean_object*)&l_instMonadST___closed__9_value;
LEAN_EXPORT lean_object* l_instMonadST(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyST___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadFinallyST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadFinallyST___closed__0 = (const lean_object*)&l_instMonadFinallyST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadFinallyST(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedST___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedST___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedST(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachST___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachST___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachST___closed__0 = (const lean_object*)&l_instMonadAttachST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachST(lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_Out_error_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EST_pure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_bind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_throw___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EST_throw___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_throw(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_throw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_tryCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EST_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEST___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__0 = (const lean_object*)&l_instMonadEST___closed__0_value;
static const lean_closure_object l_instMonadEST___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__1 = (const lean_object*)&l_instMonadEST___closed__1_value;
static const lean_closure_object l_instMonadEST___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__2 = (const lean_object*)&l_instMonadEST___closed__2_value;
static const lean_closure_object l_instMonadEST___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__3 = (const lean_object*)&l_instMonadEST___closed__3_value;
static const lean_closure_object l_instMonadEST___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__4___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__4 = (const lean_object*)&l_instMonadEST___closed__4_value;
static const lean_closure_object l_instMonadEST___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEST___lam__5___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadEST___closed__5 = (const lean_object*)&l_instMonadEST___closed__5_value;
static const lean_ctor_object l_instMonadEST___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEST___closed__0_value),((lean_object*)&l_instMonadEST___closed__1_value)}};
static const lean_object* l_instMonadEST___closed__6 = (const lean_object*)&l_instMonadEST___closed__6_value;
static const lean_ctor_object l_instMonadEST___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEST___closed__6_value),((lean_object*)&l_instMonadEST___closed__2_value),((lean_object*)&l_instMonadEST___closed__3_value),((lean_object*)&l_instMonadEST___closed__4_value),((lean_object*)&l_instMonadEST___closed__5_value)}};
static const lean_object* l_instMonadEST___closed__7 = (const lean_object*)&l_instMonadEST___closed__7_value;
static const lean_closure_object l_instMonadEST___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EST_bind___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEST___closed__8 = (const lean_object*)&l_instMonadEST___closed__8_value;
static const lean_ctor_object l_instMonadEST___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEST___closed__7_value),((lean_object*)&l_instMonadEST___closed__8_value)}};
static const lean_object* l_instMonadEST___closed__9 = (const lean_object*)&l_instMonadEST___closed__9_value;
LEAN_EXPORT lean_object* l_instMonadEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEST___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadFinallyEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadFinallyEST___closed__0 = (const lean_object*)&l_instMonadFinallyEST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadFinallyEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEST___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachEST___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachEST___closed__0 = (const lean_object*)&l_instMonadAttachEST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachEST(lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EST_throw___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEST___closed__0 = (const lean_object*)&l_instMonadExceptOfEST___closed__0_value;
static const lean_closure_object l_instMonadExceptOfEST___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_EST_tryCatch___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEST___closed__1 = (const lean_object*)&l_instMonadExceptOfEST___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfEST___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfEST___closed__0_value),((lean_object*)&l_instMonadExceptOfEST___closed__1_value)}};
static const lean_object* l_instMonadExceptOfEST___closed__2 = (const lean_object*)&l_instMonadExceptOfEST___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEST(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSTWorldOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSTWorldOfMonadLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSTWorldST(lean_object*);
LEAN_EXPORT lean_object* l_instSTWorldEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_runEST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_runEST(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_runST___redArg(lean_object*);
LEAN_EXPORT lean_object* l_runST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftSTEST___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftSTEST___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadLiftSTEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftSTEST___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadLiftSTEST___closed__0 = (const lean_object*)&l_instMonadLiftSTEST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadLiftSTEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_RefPointed;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_st_ref_ptr_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_ptrEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_mkRef___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_mkRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_swap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_swap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_take(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_ptrEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_ptrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_modifyGet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_modifyGet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Void_nonemptyType(lean_object* v_00_u03c3_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Void_mk___boxed(lean_object* v_00_u03c3_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lean_void_mk(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_ST_pure___redArg(lean_object* v_x_8_){
_start:
{
lean_inc(v_x_8_);
return v_x_8_;
}
}
LEAN_EXPORT lean_object* l_ST_pure___redArg___boxed(lean_object* v_x_10_, lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_ST_pure___redArg(v_x_10_);
lean_dec(v_x_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_ST_pure(lean_object* v_00_u03b1_13_, lean_object* v_00_u03c3_14_, lean_object* v_x_15_){
_start:
{
lean_inc(v_x_15_);
return v_x_15_;
}
}
LEAN_EXPORT lean_object* l_ST_pure___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03c3_18_, lean_object* v_x_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_ST_pure(v_00_u03b1_17_, v_00_u03c3_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_ST_bind___redArg(lean_object* v_x_22_, lean_object* v_f_23_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_apply_1(v_x_22_, lean_box(0));
v___x_26_ = lean_apply_2(v_f_23_, v___x_25_, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_ST_bind___redArg___boxed(lean_object* v_x_27_, lean_object* v_f_28_, lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_ST_bind___redArg(v_x_27_, v_f_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_ST_bind(lean_object* v_00_u03c3_31_, lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_x_34_, lean_object* v_f_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_x_34_, lean_box(0));
v___x_38_ = lean_apply_2(v_f_35_, v___x_37_, lean_box(0));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_ST_bind___boxed(lean_object* v_00_u03c3_39_, lean_object* v_00_u03b1_40_, lean_object* v_00_u03b2_41_, lean_object* v_x_42_, lean_object* v_f_43_, lean_object* v_s_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_ST_bind(v_00_u03c3_39_, v_00_u03b1_40_, v_00_u03b2_41_, v_x_42_, v_f_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__0(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v_f_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_apply_1(v_x_49_, lean_box(0));
v___x_52_ = lean_apply_1(v_f_48_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__0___boxed(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_f_55_, lean_object* v_x_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_instMonadST___lam__0(v_00_u03b1_53_, v_00_u03b2_54_, v_f_55_, v_x_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__1(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_apply_1(v___y_62_, lean_box(0));
lean_dec(v___x_64_);
lean_inc(v___y_61_);
return v___y_61_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__1___boxed(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_instMonadST___lam__1(v_00_u03b1_65_, v_00_u03b2_66_, v___y_67_, v___y_68_);
lean_dec(v___y_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__2(lean_object* v_00_u03b1_71_, lean_object* v___y_72_){
_start:
{
lean_inc(v___y_72_);
return v___y_72_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__2___boxed(lean_object* v_00_u03b1_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_instMonadST___lam__2(v_00_u03b1_74_, v___y_75_);
lean_dec(v___y_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__3(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_f_80_, lean_object* v_x_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_apply_1(v_f_80_, lean_box(0));
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_2(v_x_81_, v___x_84_, lean_box(0));
v___x_86_ = lean_apply_1(v___x_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__3___boxed(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_f_89_, lean_object* v_x_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_instMonadST___lam__3(v_00_u03b1_87_, v_00_u03b2_88_, v_f_89_, v_x_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__4(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_apply_1(v_x_95_, lean_box(0));
v___x_99_ = lean_box(0);
v___x_100_ = lean_apply_2(v_y_96_, v___x_99_, lean_box(0));
lean_dec(v___x_100_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__4___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_x_103_, lean_object* v_y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_instMonadST___lam__4(v_00_u03b1_101_, v_00_u03b2_102_, v_x_103_, v_y_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__5(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_x_109_, lean_object* v_y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_apply_1(v_x_109_, lean_box(0));
lean_dec(v___x_112_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_2(v_y_110_, v___x_113_, lean_box(0));
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_instMonadST___lam__5___boxed(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_x_117_, lean_object* v_y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_instMonadST___lam__5(v_00_u03b1_115_, v_00_u03b2_116_, v_x_117_, v_y_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_instMonadST(lean_object* v_00_u03c3_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_instMonadST___closed__9));
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyST___lam__0(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_x_144_, lean_object* v_f_145_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_apply_1(v_x_144_, lean_box(0));
lean_inc(v___x_147_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
v___x_149_ = lean_apply_2(v_f_145_, v___x_148_, lean_box(0));
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_147_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyST___lam__0___boxed(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_x_153_, lean_object* v_f_154_, lean_object* v_s_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_instMonadFinallyST___lam__0(v_00_u03b1_151_, v_00_u03b2_152_, v_x_153_, v_f_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyST(lean_object* v_00_u03c3_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = ((lean_object*)(l_instMonadFinallyST___closed__0));
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedST___redArg___lam__0(lean_object* v_inst_160_){
_start:
{
lean_inc(v_inst_160_);
return v_inst_160_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedST___redArg___lam__0___boxed(lean_object* v_inst_162_, lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_instInhabitedST___redArg___lam__0(v_inst_162_);
lean_dec(v_inst_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedST___redArg(lean_object* v_inst_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = lean_alloc_closure((void*)(l_instInhabitedST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_166_, 0, v_inst_165_);
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedST(lean_object* v_00_u03c3_167_, lean_object* v_00_u03b1_168_, lean_object* v_inst_169_){
_start:
{
lean_object* v___f_170_; 
v___f_170_ = lean_alloc_closure((void*)(l_instInhabitedST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_170_, 0, v_inst_169_);
return v___f_170_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachST___lam__0(lean_object* v_00_u03b1_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_apply_1(v_x_172_, lean_box(0));
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachST___lam__0___boxed(lean_object* v_00_u03b1_175_, lean_object* v_x_176_, lean_object* v_s_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_instMonadAttachST___lam__0(v_00_u03b1_175_, v_x_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachST(lean_object* v_00_u03c3_180_){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = ((lean_object*)(l_instMonadAttachST___closed__0));
return v___f_181_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___redArg(lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(0u);
return v___x_183_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(1u);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___redArg___boxed(lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_EST_Out_ctorIdx___redArg(v_x_185_);
lean_dec_ref(v_x_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx(lean_object* v_00_u03b5_187_, lean_object* v_00_u03c3_188_, lean_object* v_00_u03b1_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_EST_Out_ctorIdx___redArg(v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorIdx___boxed(lean_object* v_00_u03b5_192_, lean_object* v_00_u03c3_193_, lean_object* v_00_u03b1_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_EST_Out_ctorIdx(v_00_u03b5_192_, v_00_u03c3_193_, v_00_u03b1_194_, v_x_195_);
lean_dec_ref(v_x_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorElim___redArg(lean_object* v_t_197_, lean_object* v_k_198_){
_start:
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v_t_197_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v_t_197_);
v___x_200_ = lean_apply_2(v_k_198_, v_a_199_, lean_box(0));
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorElim(lean_object* v_00_u03b5_201_, lean_object* v_00_u03c3_202_, lean_object* v_00_u03b1_203_, lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_EST_Out_ctorElim___redArg(v_t_206_, v_k_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ctorElim___boxed(lean_object* v_00_u03b5_210_, lean_object* v_00_u03c3_211_, lean_object* v_00_u03b1_212_, lean_object* v_motive_213_, lean_object* v_ctorIdx_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_k_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_EST_Out_ctorElim(v_00_u03b5_210_, v_00_u03c3_211_, v_00_u03b1_212_, v_motive_213_, v_ctorIdx_214_, v_t_215_, v_h_216_, v_k_217_);
lean_dec(v_ctorIdx_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ok_elim___redArg(lean_object* v_t_219_, lean_object* v_ok_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_EST_Out_ctorElim___redArg(v_t_219_, v_ok_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_ok_elim(lean_object* v_00_u03b5_222_, lean_object* v_00_u03c3_223_, lean_object* v_00_u03b1_224_, lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_ok_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_EST_Out_ctorElim___redArg(v_t_226_, v_ok_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_error_elim___redArg(lean_object* v_t_230_, lean_object* v_error_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_EST_Out_ctorElim___redArg(v_t_230_, v_error_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_EST_Out_error_elim(lean_object* v_00_u03b5_233_, lean_object* v_00_u03c3_234_, lean_object* v_00_u03b1_235_, lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_error_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_EST_Out_ctorElim___redArg(v_t_237_, v_error_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_EST_pure___redArg(lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_EST_pure___redArg___boxed(lean_object* v_a_244_, lean_object* v_s_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_EST_pure___redArg(v_a_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_EST_pure(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b5_248_, lean_object* v_00_u03c3_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_a_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_EST_pure___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b5_254_, lean_object* v_00_u03c3_255_, lean_object* v_a_256_, lean_object* v_s_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_EST_pure(v_00_u03b1_253_, v_00_u03b5_254_, v_00_u03c3_255_, v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_EST_bind___redArg(lean_object* v_x_259_, lean_object* v_f_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_apply_1(v_x_259_, lean_box(0));
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v___x_262_);
v___x_264_ = lean_apply_2(v_f_260_, v_a_263_, lean_box(0));
return v___x_264_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_f_260_);
v_a_265_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_262_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EST_bind___redArg___boxed(lean_object* v_x_273_, lean_object* v_f_274_, lean_object* v_s_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_EST_bind___redArg(v_x_273_, v_f_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_EST_bind(lean_object* v_00_u03b5_277_, lean_object* v_00_u03c3_278_, lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_x_281_, lean_object* v_f_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_apply_1(v_x_281_, lean_box(0));
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = lean_apply_2(v_f_282_, v_a_285_, lean_box(0));
return v___x_286_;
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_f_282_);
v_a_287_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_284_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_284_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EST_bind___boxed(lean_object* v_00_u03b5_295_, lean_object* v_00_u03c3_296_, lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_x_299_, lean_object* v_f_300_, lean_object* v_s_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_EST_bind(v_00_u03b5_295_, v_00_u03c3_296_, v_00_u03b1_297_, v_00_u03b2_298_, v_x_299_, v_f_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_EST_throw___redArg(lean_object* v_e_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_e_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_EST_throw___redArg___boxed(lean_object* v_e_306_, lean_object* v_s_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_EST_throw___redArg(v_e_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_EST_throw(lean_object* v_00_u03b5_309_, lean_object* v_00_u03c3_310_, lean_object* v_00_u03b1_311_, lean_object* v_e_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_e_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_EST_throw___boxed(lean_object* v_00_u03b5_315_, lean_object* v_00_u03c3_316_, lean_object* v_00_u03b1_317_, lean_object* v_e_318_, lean_object* v_s_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_EST_throw(v_00_u03b5_315_, v_00_u03c3_316_, v_00_u03b1_317_, v_e_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_EST_tryCatch___redArg(lean_object* v_x_321_, lean_object* v_handle_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_apply_1(v_x_321_, lean_box(0));
if (lean_obj_tag(v___x_324_) == 0)
{
lean_dec_ref(v_handle_322_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v___x_324_);
v___x_326_ = lean_apply_2(v_handle_322_, v_a_325_, lean_box(0));
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_EST_tryCatch___redArg___boxed(lean_object* v_x_327_, lean_object* v_handle_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_EST_tryCatch___redArg(v_x_327_, v_handle_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_EST_tryCatch(lean_object* v_00_u03b5_331_, lean_object* v_00_u03c3_332_, lean_object* v_00_u03b1_333_, lean_object* v_x_334_, lean_object* v_handle_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_apply_1(v_x_334_, lean_box(0));
if (lean_obj_tag(v___x_337_) == 0)
{
lean_dec_ref(v_handle_335_);
return v___x_337_;
}
else
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref(v___x_337_);
v___x_339_ = lean_apply_2(v_handle_335_, v_a_338_, lean_box(0));
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_EST_tryCatch___boxed(lean_object* v_00_u03b5_340_, lean_object* v_00_u03c3_341_, lean_object* v_00_u03b1_342_, lean_object* v_x_343_, lean_object* v_handle_344_, lean_object* v_s_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_EST_tryCatch(v_00_u03b5_340_, v_00_u03c3_341_, v_00_u03b1_342_, v_x_343_, v_handle_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__0(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_f_349_, lean_object* v_x_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_1(v_x_350_, lean_box(0));
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_361_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_apply_1(v_f_349_, v_a_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_357_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_f_349_);
v_a_362_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_352_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_f_372_, lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_instMonadEST___lam__0(v_00_u03b1_370_, v_00_u03b2_371_, v_f_372_, v_x_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__1(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_apply_1(v___y_379_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; 
v_unused_389_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_389_);
v___x_383_ = v___x_381_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_dec(v___x_381_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___y_378_);
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___y_378_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v___y_378_);
v_a_390_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_381_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_381_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__1___boxed(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_instMonadEST___lam__1(v_00_u03b1_398_, v_00_u03b2_399_, v___y_400_, v___y_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__2(lean_object* v_00_u03b1_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__2___boxed(lean_object* v_00_u03b1_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_instMonadEST___lam__2(v_00_u03b1_408_, v___y_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__3(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_f_414_, lean_object* v_x_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_apply_1(v_f_414_, lean_box(0));
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v___x_417_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_2(v_x_415_, v___x_419_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_apply_1(v_a_418_, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_a_418_);
v_a_430_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_420_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_x_415_);
v_a_438_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_417_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_417_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__3___boxed(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_f_448_, lean_object* v_x_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_instMonadEST___lam__3(v_00_u03b1_446_, v_00_u03b2_447_, v_f_448_, v_x_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__4(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b2_453_, lean_object* v_x_454_, lean_object* v_y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_apply_1(v_x_454_, lean_box(0));
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_apply_2(v_y_455_, v___x_459_, lean_box(0));
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_460_, 0);
lean_dec(v_unused_468_);
v___x_462_ = v___x_460_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_dec(v___x_460_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v_a_458_);
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_458_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_a_458_);
v_a_469_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_460_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_460_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_dec_ref(v_y_455_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__4___boxed(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_instMonadEST___lam__4(v_00_u03b1_477_, v_00_u03b2_478_, v_x_479_, v_y_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__5(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_x_485_, lean_object* v_y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_apply_1(v_x_485_, lean_box(0));
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref(v___x_488_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_apply_2(v_y_486_, v___x_489_, lean_box(0));
return v___x_490_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v_y_486_);
v_a_491_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_488_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEST___lam__5___boxed(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_x_501_, lean_object* v_y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_instMonadEST___lam__5(v_00_u03b1_499_, v_00_u03b2_500_, v_x_501_, v_y_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_instMonadEST(lean_object* v_00_u03b5_524_, lean_object* v_00_u03c3_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l_instMonadEST___closed__9));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEST___lam__0(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_f_530_){
_start:
{
lean_object* v_r_532_; 
v_r_532_ = lean_apply_1(v_x_529_, lean_box(0));
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_558_; 
v_a_533_ = lean_ctor_get(v_r_532_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_r_532_);
if (v_isSharedCheck_558_ == 0)
{
v___x_535_ = v_r_532_;
v_isShared_536_ = v_isSharedCheck_558_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v_r_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_558_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
lean_inc(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 1);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_557_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_apply_2(v_f_530_, v___x_538_, lean_box(0));
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_533_);
lean_ctor_set(v___x_544_, 1, v_a_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_533_);
v_a_549_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_539_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_a_559_ = lean_ctor_get(v_r_532_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v_r_532_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_2(v_f_530_, v___x_560_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v___x_561_, 0);
lean_dec(v_unused_569_);
v___x_563_ = v___x_561_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_dec(v___x_561_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 1);
lean_ctor_set(v___x_563_, 0, v_a_559_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_559_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_559_);
v_a_570_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_561_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_561_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_f_581_, lean_object* v_s_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_instMonadFinallyEST___lam__0(v_00_u03b1_578_, v_00_u03b2_579_, v_x_580_, v_f_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEST(lean_object* v_00_u03b5_585_, lean_object* v_00_u03c3_586_){
_start:
{
lean_object* v___f_587_; 
v___f_587_ = ((lean_object*)(l_instMonadFinallyEST___closed__0));
return v___f_587_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEST___lam__0(lean_object* v_00_u03b1_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_apply_1(v_x_589_, lean_box(0));
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEST___lam__0___boxed(lean_object* v_00_u03b1_608_, lean_object* v_x_609_, lean_object* v_s_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_instMonadAttachEST___lam__0(v_00_u03b1_608_, v_x_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEST(lean_object* v_00_u03b5_613_, lean_object* v_00_u03c3_614_){
_start:
{
lean_object* v___f_615_; 
v___f_615_ = ((lean_object*)(l_instMonadAttachEST___closed__0));
return v___f_615_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEST(lean_object* v_00_u03b5_621_, lean_object* v_00_u03c3_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_instMonadExceptOfEST___closed__2));
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg___lam__0(lean_object* v_inst_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_inst_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object* v_inst_627_, lean_object* v_s_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_instInhabitedEST___redArg___lam__0(v_inst_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEST___redArg(lean_object* v_inst_630_){
_start:
{
lean_object* v___f_631_; 
v___f_631_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_631_, 0, v_inst_630_);
return v___f_631_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEST(lean_object* v_00_u03b5_632_, lean_object* v_00_u03c3_633_, lean_object* v_00_u03b1_634_, lean_object* v_inst_635_){
_start:
{
lean_object* v___f_636_; 
v___f_636_ = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_636_, 0, v_inst_635_);
return v___f_636_;
}
}
LEAN_EXPORT lean_object* l_instSTWorldOfMonadLift(lean_object* v_00_u03c3_637_, lean_object* v_m_638_, lean_object* v_n_639_, lean_object* v_inst_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_box(0);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_instSTWorldOfMonadLift___boxed(lean_object* v_00_u03c3_643_, lean_object* v_m_644_, lean_object* v_n_645_, lean_object* v_inst_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_instSTWorldOfMonadLift(v_00_u03c3_643_, v_m_644_, v_n_645_, v_inst_646_, v_inst_647_);
lean_dec(v_inst_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_instSTWorldST(lean_object* v_00_u03c3_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_instSTWorldEST(lean_object* v_00_u03b5_651_, lean_object* v_00_u03c3_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lean_box(0);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_runEST___redArg(lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = lean_void_mk(v___x_655_);
v___x_657_ = lean_apply_2(v_x_654_, lean_box(0), v___x_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 1);
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_657_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_runEST(lean_object* v_00_u03b5_674_, lean_object* v_00_u03b1_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_runEST___redArg(v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_runST___redArg(lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_box(0);
v___x_680_ = lean_void_mk(v___x_679_);
v___x_681_ = lean_apply_2(v_x_678_, lean_box(0), v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_runST(lean_object* v_00_u03b1_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_runST___redArg(v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftSTEST___lam__0(lean_object* v_00_u03b1_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_apply_1(v_x_686_, lean_box(0));
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftSTEST___lam__0___boxed(lean_object* v_00_u03b1_690_, lean_object* v_x_691_, lean_object* v_s_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_instMonadLiftSTEST___lam__0(v_00_u03b1_690_, v_x_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftSTEST(lean_object* v_00_u03b5_695_, lean_object* v_00_u03c3_696_){
_start:
{
lean_object* v___f_697_; 
v___f_697_ = ((lean_object*)(l_instMonadLiftSTEST___closed__0));
return v___f_697_;
}
}
static lean_object* _init_l_ST_RefPointed(void){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_mkRef___boxed(lean_object* v_00_u03c3_703_, lean_object* v_00_u03b1_704_, lean_object* v_a_705_, lean_object* v_a_00___x40___internal___hyg_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = lean_st_mk_ref(v_a_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_get___boxed(lean_object* v_00_u03c3_712_, lean_object* v_00_u03b1_713_, lean_object* v_r_714_, lean_object* v_a_00___x40___internal___hyg_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = lean_st_ref_get(v_r_714_);
lean_dec(v_r_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_set___boxed(lean_object* v_00_u03c3_722_, lean_object* v_00_u03b1_723_, lean_object* v_r_724_, lean_object* v_a_725_, lean_object* v_a_00___x40___internal___hyg_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = lean_st_ref_set(v_r_724_, v_a_725_);
lean_dec(v_r_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_swap___boxed(lean_object* v_00_u03c3_733_, lean_object* v_00_u03b1_734_, lean_object* v_r_735_, lean_object* v_a_736_, lean_object* v_a_00___x40___internal___hyg_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = lean_st_ref_swap(v_r_735_, v_a_736_);
lean_dec(v_r_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_take___boxed(lean_object* v_00_u03c3_743_, lean_object* v_00_u03b1_744_, lean_object* v_r_745_, lean_object* v_a_00___x40___internal___hyg_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = lean_st_ref_take(v_r_745_);
lean_dec(v_r_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_ptrEq___boxed(lean_object* v_00_u03c3_753_, lean_object* v_00_u03b1_754_, lean_object* v_r1_755_, lean_object* v_r2_756_, lean_object* v_a_00___x40___internal___hyg_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = lean_st_ref_ptr_eq(v_r1_755_, v_r2_756_);
lean_dec(v_r2_756_);
lean_dec(v_r1_755_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___redArg(lean_object* v_r_760_, lean_object* v_f_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_st_ref_take(v_r_760_);
v___x_764_ = lean_apply_1(v_f_761_, v___x_763_);
v___x_765_ = lean_st_ref_set(v_r_760_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___redArg___boxed(lean_object* v_r_766_, lean_object* v_f_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_ST_Prim_Ref_modifyUnsafe___redArg(v_r_766_, v_f_767_);
lean_dec(v_r_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe(lean_object* v_00_u03c3_770_, lean_object* v_00_u03b1_771_, lean_object* v_r_772_, lean_object* v_f_773_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_st_ref_take(v_r_772_);
v___x_776_ = lean_apply_1(v_f_773_, v___x_775_);
v___x_777_ = lean_st_ref_set(v_r_772_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyUnsafe___boxed(lean_object* v_00_u03c3_778_, lean_object* v_00_u03b1_779_, lean_object* v_r_780_, lean_object* v_f_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_ST_Prim_Ref_modifyUnsafe(v_00_u03c3_778_, v_00_u03b1_779_, v_r_780_, v_f_781_);
lean_dec(v_r_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___redArg(lean_object* v_r_784_, lean_object* v_f_785_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_791_; 
v___x_787_ = lean_st_ref_take(v_r_784_);
v___x_788_ = lean_apply_1(v_f_785_, v___x_787_);
v_fst_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_fst_789_);
v_snd_790_ = lean_ctor_get(v___x_788_, 1);
lean_inc(v_snd_790_);
lean_dec_ref(v___x_788_);
v___x_791_ = lean_st_ref_set(v_r_784_, v_snd_790_);
return v_fst_789_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___redArg___boxed(lean_object* v_r_792_, lean_object* v_f_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_ST_Prim_Ref_modifyGetUnsafe___redArg(v_r_792_, v_f_793_);
lean_dec(v_r_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe(lean_object* v_00_u03c3_796_, lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_r_799_, lean_object* v_f_800_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_806_; 
v___x_802_ = lean_st_ref_take(v_r_799_);
v___x_803_ = lean_apply_1(v_f_800_, v___x_802_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_fst_804_);
v_snd_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_snd_805_);
lean_dec_ref(v___x_803_);
v___x_806_ = lean_st_ref_set(v_r_799_, v_snd_805_);
return v_fst_804_;
}
}
LEAN_EXPORT lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object* v_00_u03c3_807_, lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_r_810_, lean_object* v_f_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_ST_Prim_Ref_modifyGetUnsafe(v_00_u03c3_807_, v_00_u03b1_808_, v_00_u03b2_809_, v_r_810_, v_f_811_);
lean_dec(v_r_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_ST_mkRef___redArg(lean_object* v_inst_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_816_, 0, lean_box(0));
lean_closure_set(v___x_816_, 1, lean_box(0));
lean_closure_set(v___x_816_, 2, v_a_815_);
v___x_817_ = lean_apply_2(v_inst_814_, lean_box(0), v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_ST_mkRef(lean_object* v_00_u03c3_818_, lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_00_u03b1_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_823_, 0, lean_box(0));
lean_closure_set(v___x_823_, 1, lean_box(0));
lean_closure_set(v___x_823_, 2, v_a_822_);
v___x_824_ = lean_apply_2(v_inst_820_, lean_box(0), v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_get___redArg(lean_object* v_inst_825_, lean_object* v_r_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_827_, 0, lean_box(0));
lean_closure_set(v___x_827_, 1, lean_box(0));
lean_closure_set(v___x_827_, 2, v_r_826_);
v___x_828_ = lean_apply_2(v_inst_825_, lean_box(0), v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_get(lean_object* v_00_u03c3_829_, lean_object* v_m_830_, lean_object* v_inst_831_, lean_object* v_00_u03b1_832_, lean_object* v_r_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_834_, 0, lean_box(0));
lean_closure_set(v___x_834_, 1, lean_box(0));
lean_closure_set(v___x_834_, 2, v_r_833_);
v___x_835_ = lean_apply_2(v_inst_831_, lean_box(0), v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_set___redArg(lean_object* v_inst_836_, lean_object* v_r_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_839_, 0, lean_box(0));
lean_closure_set(v___x_839_, 1, lean_box(0));
lean_closure_set(v___x_839_, 2, v_r_837_);
lean_closure_set(v___x_839_, 3, v_a_838_);
v___x_840_ = lean_apply_2(v_inst_836_, lean_box(0), v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_set(lean_object* v_00_u03c3_841_, lean_object* v_m_842_, lean_object* v_inst_843_, lean_object* v_00_u03b1_844_, lean_object* v_r_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_847_, 0, lean_box(0));
lean_closure_set(v___x_847_, 1, lean_box(0));
lean_closure_set(v___x_847_, 2, v_r_845_);
lean_closure_set(v___x_847_, 3, v_a_846_);
v___x_848_ = lean_apply_2(v_inst_843_, lean_box(0), v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_swap___redArg(lean_object* v_inst_849_, lean_object* v_r_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_852_, 0, lean_box(0));
lean_closure_set(v___x_852_, 1, lean_box(0));
lean_closure_set(v___x_852_, 2, v_r_850_);
lean_closure_set(v___x_852_, 3, v_a_851_);
v___x_853_ = lean_apply_2(v_inst_849_, lean_box(0), v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_swap(lean_object* v_00_u03c3_854_, lean_object* v_m_855_, lean_object* v_inst_856_, lean_object* v_00_u03b1_857_, lean_object* v_r_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_860_, 0, lean_box(0));
lean_closure_set(v___x_860_, 1, lean_box(0));
lean_closure_set(v___x_860_, 2, v_r_858_);
lean_closure_set(v___x_860_, 3, v_a_859_);
v___x_861_ = lean_apply_2(v_inst_856_, lean_box(0), v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_take___redArg(lean_object* v_inst_862_, lean_object* v_r_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_take___boxed), 4, 3);
lean_closure_set(v___x_864_, 0, lean_box(0));
lean_closure_set(v___x_864_, 1, lean_box(0));
lean_closure_set(v___x_864_, 2, v_r_863_);
v___x_865_ = lean_apply_2(v_inst_862_, lean_box(0), v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_take(lean_object* v_00_u03c3_866_, lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_00_u03b1_869_, lean_object* v_r_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_take___boxed), 4, 3);
lean_closure_set(v___x_871_, 0, lean_box(0));
lean_closure_set(v___x_871_, 1, lean_box(0));
lean_closure_set(v___x_871_, 2, v_r_870_);
v___x_872_ = lean_apply_2(v_inst_868_, lean_box(0), v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_ptrEq___redArg(lean_object* v_inst_873_, lean_object* v_r1_874_, lean_object* v_r2_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_ptrEq___boxed), 5, 4);
lean_closure_set(v___x_876_, 0, lean_box(0));
lean_closure_set(v___x_876_, 1, lean_box(0));
lean_closure_set(v___x_876_, 2, v_r1_874_);
lean_closure_set(v___x_876_, 3, v_r2_875_);
v___x_877_ = lean_apply_2(v_inst_873_, lean_box(0), v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_ptrEq(lean_object* v_00_u03c3_878_, lean_object* v_m_879_, lean_object* v_inst_880_, lean_object* v_00_u03b1_881_, lean_object* v_r1_882_, lean_object* v_r2_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_ptrEq___boxed), 5, 4);
lean_closure_set(v___x_884_, 0, lean_box(0));
lean_closure_set(v___x_884_, 1, lean_box(0));
lean_closure_set(v___x_884_, 2, v_r1_882_);
lean_closure_set(v___x_884_, 3, v_r2_883_);
v___x_885_ = lean_apply_2(v_inst_880_, lean_box(0), v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_modify___redArg(lean_object* v_inst_886_, lean_object* v_r_887_, lean_object* v_f_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyUnsafe___boxed), 5, 4);
lean_closure_set(v___x_889_, 0, lean_box(0));
lean_closure_set(v___x_889_, 1, lean_box(0));
lean_closure_set(v___x_889_, 2, v_r_887_);
lean_closure_set(v___x_889_, 3, v_f_888_);
v___x_890_ = lean_apply_2(v_inst_886_, lean_box(0), v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_modify(lean_object* v_00_u03c3_891_, lean_object* v_m_892_, lean_object* v_inst_893_, lean_object* v_00_u03b1_894_, lean_object* v_r_895_, lean_object* v_f_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyUnsafe___boxed), 5, 4);
lean_closure_set(v___x_897_, 0, lean_box(0));
lean_closure_set(v___x_897_, 1, lean_box(0));
lean_closure_set(v___x_897_, 2, v_r_895_);
lean_closure_set(v___x_897_, 3, v_f_896_);
v___x_898_ = lean_apply_2(v_inst_893_, lean_box(0), v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_modifyGet___redArg(lean_object* v_inst_899_, lean_object* v_r_900_, lean_object* v_f_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_902_, 0, lean_box(0));
lean_closure_set(v___x_902_, 1, lean_box(0));
lean_closure_set(v___x_902_, 2, lean_box(0));
lean_closure_set(v___x_902_, 3, v_r_900_);
lean_closure_set(v___x_902_, 4, v_f_901_);
v___x_903_ = lean_apply_2(v_inst_899_, lean_box(0), v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_modifyGet(lean_object* v_00_u03c3_904_, lean_object* v_m_905_, lean_object* v_inst_906_, lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_r_909_, lean_object* v_f_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_911_, 0, lean_box(0));
lean_closure_set(v___x_911_, 1, lean_box(0));
lean_closure_set(v___x_911_, 2, lean_box(0));
lean_closure_set(v___x_911_, 3, v_r_909_);
lean_closure_set(v___x_911_, 4, v_f_910_);
v___x_912_ = lean_apply_2(v_inst_906_, lean_box(0), v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf___redArg___lam__0(lean_object* v_r_913_, lean_object* v_inst_914_, lean_object* v_00_u03b1_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_917_, 0, lean_box(0));
lean_closure_set(v___x_917_, 1, lean_box(0));
lean_closure_set(v___x_917_, 2, lean_box(0));
lean_closure_set(v___x_917_, 3, v_r_913_);
lean_closure_set(v___x_917_, 4, v___y_916_);
v___x_918_ = lean_apply_2(v_inst_914_, lean_box(0), v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf___redArg(lean_object* v_inst_919_, lean_object* v_r_920_){
_start:
{
lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_inc(v_inst_919_);
lean_inc(v_r_920_);
v___f_921_ = lean_alloc_closure((void*)(l_ST_Ref_toMonadStateOf___redArg___lam__0), 4, 2);
lean_closure_set(v___f_921_, 0, v_r_920_);
lean_closure_set(v___f_921_, 1, v_inst_919_);
lean_inc(v_r_920_);
v___x_922_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_922_, 0, lean_box(0));
lean_closure_set(v___x_922_, 1, lean_box(0));
lean_closure_set(v___x_922_, 2, v_r_920_);
lean_inc(v_inst_919_);
v___x_923_ = lean_apply_2(v_inst_919_, lean_box(0), v___x_922_);
v___x_924_ = lean_alloc_closure((void*)(l_ST_Ref_set), 6, 5);
lean_closure_set(v___x_924_, 0, lean_box(0));
lean_closure_set(v___x_924_, 1, lean_box(0));
lean_closure_set(v___x_924_, 2, v_inst_919_);
lean_closure_set(v___x_924_, 3, lean_box(0));
lean_closure_set(v___x_924_, 4, v_r_920_);
v___x_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set(v___x_925_, 2, v___f_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_ST_Ref_toMonadStateOf(lean_object* v_00_u03c3_926_, lean_object* v_m_927_, lean_object* v_inst_928_, lean_object* v_00_u03b1_929_, lean_object* v_r_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_ST_Ref_toMonadStateOf___redArg(v_inst_928_, v_r_930_);
return v___x_931_;
}
}
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_ST(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ST_RefPointed = _init_l_ST_RefPointed();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_ST(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_ST(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_ST(builtin);
}
#ifdef __cplusplus
}
#endif
