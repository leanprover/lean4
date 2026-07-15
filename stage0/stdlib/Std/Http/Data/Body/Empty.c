// Lean compiler output
// Module: Std.Http.Data.Body.Empty
// Imports: public import Std.Http.Data.Request public import Std.Http.Data.Response public import Std.Http.Data.Body.Any
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
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_object*);
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofBody___redArg(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__1 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__1;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__3 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__4 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__3_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__4_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__5 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__5_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__6 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__6_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__7;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__8 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__8_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__9;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___closed__10 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___closed__10_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___closed__11;
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
static const lean_closure_object l_Std_Http_Body_instEmpty___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_tryRecv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instEmpty___closed__6 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value;
static const lean_ctor_object l_Std_Http_Body_instEmpty___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__2_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__3_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__4_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__5_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__6_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__0_value),((lean_object*)&l_Std_Http_Body_instEmpty___closed__1_value)}};
static const lean_object* l_Std_Http_Body_instEmpty___closed__7 = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instEmpty = (const lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value;
static const lean_closure_object l_Std_Http_Body_instCoeEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofBody, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseEmptyAny___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value)} };
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Http_Body_Empty_tryRecv___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object* v_x_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object* v_x_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Http_Body_Empty_tryRecv(v_x_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0(lean_object* v___x_73_, lean_object* v_promise_74_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_73_);
v___x_77_ = lean_io_promise_resolve(v___x_76_, v_promise_74_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(lean_object* v___x_80_, lean_object* v_promise_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Http_Body_Empty_recvSelector___lam__0(v___x_80_, v_promise_81_);
lean_dec(v_promise_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1(lean_object* v___x_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(lean_object* v___x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Http_Body_Empty_recvSelector___lam__1(v___x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2(lean_object* v___x_93_, lean_object* v___f_94_, lean_object* v_win_95_, lean_object* v_waiter_96_){
_start:
{
lean_object* v_lose_98_; lean_object* v___x_266__overap_99_; lean_object* v___x_100_; 
v_lose_98_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___x_266__overap_99_ = l_Std_Async_Waiter_race___redArg(v___x_93_, v___f_94_, v_waiter_96_, v_lose_98_, v_win_95_);
v___x_100_ = lean_apply_1(v___x_266__overap_99_, lean_box(0));
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(lean_object* v___x_101_, lean_object* v___f_102_, lean_object* v_win_103_, lean_object* v_waiter_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Http_Body_Empty_recvSelector___lam__2(v___x_101_, v___f_102_, v_win_103_, v_waiter_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3(lean_object* v___x_107_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(lean_object* v___x_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Http_Body_Empty_recvSelector___lam__3(v___x_111_);
return v_res_113_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__1(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
return v___x_115_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__7(void){
_start:
{
lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___f_127_; 
v___x_125_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__1, &l_Std_Http_Body_Empty_recvSelector___closed__1_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__1);
v___f_126_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__6));
v___f_127_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_127_, 0, v___f_126_);
lean_closure_set(v___f_127_, 1, v___x_125_);
return v___f_127_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__9(void){
_start:
{
lean_object* v_win_130_; lean_object* v___f_131_; lean_object* v___x_132_; lean_object* v___f_133_; 
v_win_130_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__8));
v___f_131_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__7, &l_Std_Http_Body_Empty_recvSelector___closed__7_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__7);
v___x_132_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__0, &l_Std_Http_Body_Empty_recvSelector___closed__0_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__0);
v___f_133_ = lean_alloc_closure((void*)(l_Std_Http_Body_Empty_recvSelector___lam__2___boxed), 5, 3);
lean_closure_set(v___f_133_, 0, v___x_132_);
lean_closure_set(v___f_133_, 1, v___f_131_);
lean_closure_set(v___f_133_, 2, v_win_130_);
return v___f_133_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___closed__11(void){
_start:
{
lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_136_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0));
v___f_137_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__9, &l_Std_Http_Body_Empty_recvSelector___closed__9_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__9);
v___f_138_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___closed__10));
v___x_139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_139_, 0, v___f_138_);
lean_ctor_set(v___x_139_, 1, v___f_137_);
lean_ctor_set(v___x_139_, 2, v___f_136_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___closed__11, &l_Std_Http_Body_Empty_recvSelector___closed__11_once, _init_l_Std_Http_Body_Empty_recvSelector___closed__11);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object* v_x_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Std_Http_Body_instEmpty___lam__0___closed__3));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object* v_x_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Http_Body_instEmpty___lam__0(v_x_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Http_Body_instEmpty___lam__1(v_x_160_, v_x_161_);
lean_dec(v_x_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object* v___x_183_, lean_object* v_f_184_){
_start:
{
lean_object* v_line_185_; lean_object* v_body_186_; lean_object* v_extensions_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_line_185_ = lean_ctor_get(v_f_184_, 0);
v_body_186_ = lean_ctor_get(v_f_184_, 1);
v_extensions_187_ = lean_ctor_get(v_f_184_, 2);
v_isSharedCheck_195_ = !lean_is_exclusive(v_f_184_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v_f_184_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_extensions_187_);
lean_inc(v_body_186_);
lean_inc(v_line_185_);
lean_dec(v_f_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_183_, v_body_186_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_line_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_extensions_187_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object* v___x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v___x_199_);
v_a_202_ = lean_ctor_get(v_x_200_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v_x_200_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v_x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_230_; 
v_a_211_ = lean_ctor_get(v_x_200_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_230_ == 0)
{
v___x_213_ = v_x_200_;
v_isShared_214_ = v_isSharedCheck_230_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v_x_200_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_230_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_line_215_; lean_object* v_body_216_; lean_object* v_extensions_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_229_; 
v_line_215_ = lean_ctor_get(v_a_211_, 0);
v_body_216_ = lean_ctor_get(v_a_211_, 1);
v_extensions_217_ = lean_ctor_get(v_a_211_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_a_211_);
if (v_isSharedCheck_229_ == 0)
{
v___x_219_ = v_a_211_;
v_isShared_220_ = v_isSharedCheck_229_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_extensions_217_);
lean_inc(v_body_216_);
lean_inc(v_line_215_);
lean_dec(v_a_211_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_229_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_199_, v_body_216_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_line_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_extensions_217_);
v___x_223_ = v_reuseFailAlloc_228_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_223_);
v___x_225_ = v___x_213_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object* v___x_231_, lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_231_, v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object* v___f_235_, lean_object* v_action_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
lean_inc_ref(v___y_237_);
v___x_239_ = lean_apply_2(v_action_236_, v___y_237_, lean_box(0));
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = 0;
v___x_242_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_240_, v___x_241_, v___x_239_, v___f_235_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object* v___f_243_, lean_object* v_action_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_243_, v_action_244_, v___y_245_);
lean_dec_ref(v___y_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object* v___f_253_, lean_object* v_action_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_apply_1(v_action_254_, lean_box(0));
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = 0;
v___x_260_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_258_, v___x_259_, v___x_257_, v___f_253_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object* v___f_261_, lean_object* v_action_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_261_, v_action_262_, v___y_263_);
lean_dec_ref(v___y_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty(lean_object* v_builder_269_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_box(0);
v___x_272_ = l_Std_Http_Request_Builder_body___redArg(v_builder_269_, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object* v_builder_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Http_Request_Builder_empty(v_builder_275_);
lean_dec_ref(v_builder_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty(lean_object* v_builder_278_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_box(0);
v___x_281_ = l_Std_Http_Response_Builder_body___redArg(v_builder_278_, v___x_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object* v_builder_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Http_Response_Builder_empty(v_builder_284_);
lean_dec_ref(v_builder_284_);
return v_res_286_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Any(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Any(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
