// Lean compiler output
// Module: Std.Internal.Http.Data.Body.Empty
// Imports: public import Std.Internal.Http.Data.Request public import Std.Internal.Http.Data.Response public import Std.Internal.Http.Data.Body.Any
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
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty_default;
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty;
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instBEqEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instBEqEmpty_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instBEqEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instBEqEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instBEqEmpty = (const lean_object*)&l_Std_Http_Body_instBEqEmpty___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_recv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_recv___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_recv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_recv___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_recv___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Empty_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_close___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_close___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_close___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_close___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_isClosed___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_isClosed___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__0;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__1_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__3 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__4 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__1_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__5 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__6 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__6_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__7;
static const lean_ctor_object l_Std_Http_Body_Empty_recvSelector___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__8 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__8_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__8_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__9 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__9_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__10;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object*);
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__1_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__2_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Body_instEmpty___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instEmpty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instEmpty___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__1 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__1_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__2 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__2_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_close___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__3 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__3_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_isClosed___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__4 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__4_value;
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__5 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__5_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__2_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__3_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__4_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__5_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__0_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__1_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___closed__6 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instEmpty = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value;
static const lean_closure_object l_Std_Http_Body_instCoeEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseEmptyAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1 = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny = (const lean_object*)&l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty_default(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object* v_x_5_, lean_object* v_y_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_8_, v_y_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg(){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Http_Body_Empty_recv___redArg();
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv(lean_object* v_x_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object* v_x_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Http_Body_Empty_recv(v_x_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Http_Body_Empty_close___redArg();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close(lean_object* v_x_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object* v_x_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_Http_Body_Empty_close(v_x_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Http_Body_Empty_isClosed___redArg();
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed(lean_object* v_x_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object* v_x_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Http_Body_Empty_isClosed(v_x_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0(lean_object* v___x_57_, lean_object* v_promise_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_57_);
v___x_61_ = lean_io_promise_resolve(v___x_60_, v_promise_58_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(lean_object* v___x_64_, lean_object* v_promise_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Http_Body_Empty_recvSelector___lam__0(v___x_64_, v_promise_65_);
lean_dec(v_promise_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1(lean_object* v___x_68_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(lean_object* v___x_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Http_Body_Empty_recvSelector___lam__1(v___x_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2(lean_object* v___x_77_, lean_object* v___f_78_, lean_object* v_win_79_, lean_object* v_waiter_80_){
_start:
{
lean_object* v_lose_82_; lean_object* v___x_221__overap_83_; lean_object* v___x_84_; 
v_lose_82_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___x_221__overap_83_ = l_Std_Internal_IO_Async_Waiter_race___redArg(v___x_77_, v___f_78_, v_waiter_80_, v_lose_82_, v_win_79_);
v___x_84_ = lean_apply_1(v___x_221__overap_83_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(lean_object* v___x_85_, lean_object* v___f_86_, lean_object* v_win_87_, lean_object* v_waiter_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Http_Body_Empty_recvSelector___lam__2(v___x_85_, v___f_86_, v_win_87_, v_waiter_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3(lean_object* v___x_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(lean_object* v___x_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Http_Body_Empty_recvSelector___lam__3(v___x_95_);
return v_res_97_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__0(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_98_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__7(void){
_start:
{
lean_object* v_win_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___f_113_; 
v_win_110_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__6));
v___f_111_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__5));
v___x_112_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__0, &l_Std_Http_Body_Empty_recvSelector___closed__0_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__0);
v___f_113_ = lean_alloc_closure((void*)(l_Std_Http_Body_Empty_recvSelector___lam__2___boxed), 5, 3);
lean_closure_set(v___f_113_, 0, v___x_112_);
lean_closure_set(v___f_113_, 1, v___f_111_);
lean_closure_set(v___f_113_, 2, v_win_110_);
return v___f_113_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__10(void){
_start:
{
lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___x_121_; 
v___f_118_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___f_119_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__7, &l_Std_Http_Body_Empty_recvSelector___closed__7_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__7);
v___f_120_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__9));
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v___f_120_);
lean_ctor_set(v___x_121_, 1, v___f_119_);
lean_ctor_set(v___x_121_, 2, v___f_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__10, &l_Std_Http_Body_Empty_recvSelector___closed__10_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__10);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object* v_x_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_Std_Http_Body_instEmpty___lam__0___closed__3));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object* v_x_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Http_Body_instEmpty___lam__0(v_x_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Http_Body_instEmpty___lam__1(v_x_142_, v_x_143_);
lean_dec(v_x_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object* v___x_163_, lean_object* v_f_164_){
_start:
{
lean_object* v_line_165_; lean_object* v_body_166_; lean_object* v_extensions_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_line_165_ = lean_ctor_get(v_f_164_, 0);
v_body_166_ = lean_ctor_get(v_f_164_, 1);
v_extensions_167_ = lean_ctor_get(v_f_164_, 2);
v_isSharedCheck_175_ = !lean_is_exclusive(v_f_164_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_f_164_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_extensions_167_);
lean_inc(v_body_166_);
lean_inc(v_line_165_);
lean_dec(v_f_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_163_, v_body_166_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_line_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_extensions_167_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object* v___x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v___x_179_);
v_a_182_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v_x_180_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v_x_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_210_; 
v_a_191_ = lean_ctor_get(v_x_180_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_180_);
if (v_isSharedCheck_210_ == 0)
{
v___x_193_ = v_x_180_;
v_isShared_194_ = v_isSharedCheck_210_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v_x_180_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_210_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_line_195_; lean_object* v_body_196_; lean_object* v_extensions_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_209_; 
v_line_195_ = lean_ctor_get(v_a_191_, 0);
v_body_196_ = lean_ctor_get(v_a_191_, 1);
v_extensions_197_ = lean_ctor_get(v_a_191_, 2);
v_isSharedCheck_209_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_209_ == 0)
{
v___x_199_ = v_a_191_;
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_extensions_197_);
lean_inc(v_body_196_);
lean_inc(v_line_195_);
lean_dec(v_a_191_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_179_, v_body_196_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_line_195_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_extensions_197_);
v___x_203_ = v_reuseFailAlloc_208_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_203_);
v___x_205_ = v___x_193_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object* v___x_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_211_, v_x_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object* v___f_215_, lean_object* v_action_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v___y_217_);
v___x_219_ = lean_apply_2(v_action_216_, v___y_217_, lean_box(0));
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = 0;
v___x_222_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_220_, v___x_221_, v___x_219_, v___f_215_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object* v___f_223_, lean_object* v_action_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_223_, v_action_224_, v___y_225_);
lean_dec_ref(v___y_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object* v___f_233_, lean_object* v_action_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_apply_1(v_action_234_, lean_box(0));
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = 0;
v___x_240_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_238_, v___x_239_, v___x_237_, v___f_233_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object* v___f_241_, lean_object* v_action_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_241_, v_action_242_, v___y_243_);
lean_dec_ref(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object* v_builder_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_box(0);
v___x_252_ = l_Std_Http_Request_Builder_body___redArg(v_builder_249_, v___x_251_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object* v_builder_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Http_Request_Builder_empty(v_builder_255_);
lean_dec_ref(v_builder_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object* v_builder_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_box(0);
v___x_261_ = l_Std_Http_Response_Builder_body___redArg(v_builder_258_, v___x_260_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object* v_builder_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Http_Response_Builder_empty(v_builder_264_);
lean_dec_ref(v_builder_264_);
return v_res_266_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Body_Any(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Body_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
