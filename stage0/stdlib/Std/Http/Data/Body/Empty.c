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
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_Waiter_race___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Any_ofReplayableBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty_default;
LEAN_EXPORT lean_object* l_Std_Http_Body_instInhabitedEmpty;
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqEmpty_beq___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__0;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__1;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__2 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__3 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__4 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__3_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__4_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__5 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__5_value),((lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__2_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__6 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__7;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__8 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__8_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__9;
static const lean_closure_object l_Std_Http_Body_Empty_recvSelector___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)} };
static const lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__10 = (const lean_object*)&l_Std_Http_Body_Empty_recvSelector___redArg___closed__10_value;
static lean_once_cell_t l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instReplayableEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instReplayableEmpty___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instReplayableEmpty___closed__0 = (const lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instReplayableEmpty = (const lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instCoeEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_Any_ofReplayableBody, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeResponseEmptyAny___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
static const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___closed__0 = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instCoeResponseEmptyAny = (const lean_object*)&l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Body_instEmpty___closed__7_value),((lean_object*)&l_Std_Http_Body_instReplayableEmpty___closed__0_value)} };
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
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Std_Http_Body_instInhabitedEmpty(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
uint8_t l_Std_Http_Body_instBEqEmpty_beq___redArg(){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instBEqEmpty_beq___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_5_;
v_res_5_ = l_Std_Http_Body_instBEqEmpty_beq___redArg();
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Std_Http_Body_instBEqEmpty_beq___redArg();
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Std_Http_Body_instBEqEmpty_beq(lean_object* v_x_9_, lean_object* v_y_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = 1;
return v___x_11_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instBEqEmpty_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_9_ = stack[0].m_obj;
lean_object* v_y_10_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_9_, v_y_10_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqEmpty_beq___boxed(lean_object* v_x_13_, lean_object* v_y_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_13_, v_y_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
lean_object* l_Std_Http_Body_Empty_recv___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_24_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_25_;
v_res_25_ = l_Std_Http_Body_Empty_recv___redArg();
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___redArg___boxed(lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Http_Body_Empty_recv___redArg();
return v_res_27_;
}
}
lean_object* l_Std_Http_Body_Empty_recv(lean_object* v_x_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Std_Http_Body_Empty_recv___redArg___closed__1));
return v___x_30_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_28_ = stack[0].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Http_Body_Empty_recv(v_x_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recv___boxed(lean_object* v_x_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Http_Body_Empty_recv(v_x_32_);
return v_res_34_;
}
}
lean_object* l_Std_Http_Body_Empty_close___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_40_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_41_;
v_res_41_ = l_Std_Http_Body_Empty_close___redArg();
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___redArg___boxed(lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Http_Body_Empty_close___redArg();
return v_res_43_;
}
}
lean_object* l_Std_Http_Body_Empty_close(lean_object* v_x_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_46_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_44_ = stack[0].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Std_Http_Body_Empty_close(v_x_44_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_close___boxed(lean_object* v_x_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Http_Body_Empty_close(v_x_48_);
return v_res_50_;
}
}
lean_object* l_Std_Http_Body_Empty_isClosed___redArg(){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_57_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l_Std_Http_Body_Empty_isClosed___redArg();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___redArg___boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Http_Body_Empty_isClosed___redArg();
return v_res_60_;
}
}
lean_object* l_Std_Http_Body_Empty_isClosed(lean_object* v_x_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Std_Http_Body_Empty_isClosed___redArg___closed__1));
return v___x_63_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Std_Http_Body_Empty_isClosed(v_x_61_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_isClosed___boxed(lean_object* v_x_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Http_Body_Empty_isClosed(v_x_65_);
return v_res_67_;
}
}
lean_object* l_Std_Http_Body_Empty_tryRecv___redArg(){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_75_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_76_;
v_res_76_ = l_Std_Http_Body_Empty_tryRecv___redArg();
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___redArg___boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Http_Body_Empty_tryRecv___redArg();
return v_res_78_;
}
}
lean_object* l_Std_Http_Body_Empty_tryRecv(lean_object* v_x_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2));
return v___x_81_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
lean_object* v_res_82_;
v_res_82_ = l_Std_Http_Body_Empty_tryRecv(v_x_79_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_tryRecv___boxed(lean_object* v_x_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_Http_Body_Empty_tryRecv(v_x_83_);
return v_res_85_;
}
}
lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(lean_object* v___x_86_, lean_object* v_promise_87_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_86_);
v___x_90_ = lean_io_promise_resolve(v___x_89_, v_promise_87_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_86_ = stack[0].m_obj;
lean_object* v_promise_87_ = stack[1].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(v___x_86_, v_promise_87_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__0___boxed(lean_object* v___x_94_, lean_object* v_promise_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__0(v___x_94_, v_promise_95_);
lean_dec(v_promise_95_);
return v_res_97_;
}
}
lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(lean_object* v___x_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_98_ = stack[0].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(v___x_98_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__1___boxed(lean_object* v___x_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__1(v___x_103_);
return v_res_105_;
}
}
lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(lean_object* v___x_108_, lean_object* v___f_109_, lean_object* v_win_110_, lean_object* v_waiter_111_){
_start:
{
lean_object* v_lose_113_; lean_object* v___x_310__overap_114_; lean_object* v___x_115_; 
v_lose_113_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0));
v___x_310__overap_114_ = l_Std_Async_Waiter_race___redArg(v___x_108_, v___f_109_, v_waiter_111_, v_lose_113_, v_win_110_);
v___x_115_ = lean_apply_1(v___x_310__overap_114_, lean_box(0));
return v___x_115_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_108_ = stack[0].m_obj;
lean_object* v___f_109_ = stack[1].m_obj;
lean_object* v_win_110_ = stack[2].m_obj;
lean_object* v_waiter_111_ = stack[3].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(v___x_108_, v___f_109_, v_win_110_, v_waiter_111_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed(lean_object* v___x_117_, lean_object* v___f_118_, lean_object* v_win_119_, lean_object* v_waiter_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__2(v___x_117_, v___f_118_, v_win_119_, v_waiter_120_);
return v_res_122_;
}
}
lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(lean_object* v___x_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_123_ = stack[0].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(v___x_123_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___lam__3___boxed(lean_object* v___x_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Http_Body_Empty_recvSelector___redArg___lam__3(v___x_128_);
return v_res_130_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__0(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_131_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__1(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_132_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__7(void){
_start:
{
lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v___f_144_; 
v___x_142_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__1, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__1_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__1);
v___f_143_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__6));
v___f_144_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_144_, 0, v___f_143_);
lean_closure_set(v___f_144_, 1, v___x_142_);
return v___f_144_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__9(void){
_start:
{
lean_object* v_win_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___f_150_; 
v_win_147_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__8));
v___f_148_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__7, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__7_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__7);
v___x_149_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__0, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__0_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__0);
v___f_150_ = lean_alloc_closure((void*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_150_, 0, v___x_149_);
lean_closure_set(v___f_150_, 1, v___f_148_);
lean_closure_set(v___f_150_, 2, v_win_147_);
return v___f_150_;
}
}
static lean_object* _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11(void){
_start:
{
lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; 
v___f_153_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___lam__2___closed__0));
v___f_154_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__9, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__9_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__9);
v___f_155_ = ((lean_object*)(l_Std_Http_Body_Empty_recvSelector___redArg___closed__10));
v___x_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_156_, 0, v___f_155_);
lean_ctor_set(v___x_156_, 1, v___f_154_);
lean_ctor_set(v___x_156_, 2, v___f_153_);
return v___x_156_;
}
}
lean_object* l_Std_Http_Body_Empty_recvSelector___redArg(){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__11, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11);
return v___x_158_;
}
}
LEAN_EXPORT void l_Std_Http_Body_Empty_recvSelector___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_159_;
v_res_159_ = l_Std_Http_Body_Empty_recvSelector___redArg();
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector___redArg___boxed(lean_object* v___dummy_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Http_Body_Empty_recvSelector___redArg();
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Empty_recvSelector(lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_Http_Body_Empty_recvSelector___redArg___closed__11, &l_Std_Http_Body_Empty_recvSelector___redArg___closed__11_once, _init_l_Std_Http_Body_Empty_recvSelector___redArg___closed__11);
return v___x_163_;
}
}
lean_object* l_Std_Http_Body_instEmpty___lam__0(lean_object* v_x_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Std_Http_Body_instEmpty___lam__0___closed__3));
return v___x_174_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_172_ = stack[0].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Std_Http_Body_instEmpty___lam__0(v_x_172_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__0___boxed(lean_object* v_x_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Http_Body_instEmpty___lam__0(v_x_176_);
return v_res_178_;
}
}
lean_object* l_Std_Http_Body_instEmpty___lam__1(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_182_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instEmpty___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_179_ = stack[0].m_obj;
lean_object* v_x_180_ = stack[1].m_obj;
lean_object* v_res_183_;
v_res_183_ = l_Std_Http_Body_instEmpty___lam__1(v_x_179_, v_x_180_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instEmpty___lam__1___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Http_Body_instEmpty___lam__1(v_x_184_, v_x_185_);
lean_dec(v_x_185_);
return v_res_187_;
}
}
lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0(lean_object* v_x_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Std_Http_Body_Empty_close___redArg___closed__1));
return v___x_206_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instReplayableEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_204_ = stack[0].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Std_Http_Body_instReplayableEmpty___lam__0(v_x_204_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReplayableEmpty___lam__0___boxed(lean_object* v_x_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Http_Body_instReplayableEmpty___lam__0(v_x_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(lean_object* v___x_217_, lean_object* v___f_218_, lean_object* v_f_219_){
_start:
{
lean_object* v_line_220_; lean_object* v_body_221_; lean_object* v_extensions_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_line_220_ = lean_ctor_get(v_f_219_, 0);
v_body_221_ = lean_ctor_get(v_f_219_, 1);
v_extensions_222_ = lean_ctor_get(v_f_219_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_f_219_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v_f_219_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_extensions_222_);
lean_inc(v_body_221_);
lean_inc(v_line_220_);
lean_dec(v_f_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_217_, v___f_218_, v_body_221_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_line_220_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_extensions_222_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(lean_object* v___x_235_, lean_object* v___f_236_, lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v___f_236_);
lean_dec_ref(v___x_235_);
v_a_239_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_x_237_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v_x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_267_; 
v_a_248_ = lean_ctor_get(v_x_237_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_267_ == 0)
{
v___x_250_ = v_x_237_;
v_isShared_251_ = v_isSharedCheck_267_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v_x_237_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_267_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_line_252_; lean_object* v_body_253_; lean_object* v_extensions_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_266_; 
v_line_252_ = lean_ctor_get(v_a_248_, 0);
v_body_253_ = lean_ctor_get(v_a_248_, 1);
v_extensions_254_ = lean_ctor_get(v_a_248_, 2);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_248_);
if (v_isSharedCheck_266_ == 0)
{
v___x_256_ = v_a_248_;
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_extensions_254_);
lean_inc(v_body_253_);
lean_inc(v_line_252_);
lean_dec(v_a_248_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = l_Std_Http_Body_Any_ofReplayableBody___redArg(v___x_235_, v___f_236_, v_body_253_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_line_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_extensions_254_);
v___x_260_ = v_reuseFailAlloc_265_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_260_);
v___x_262_ = v___x_250_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_264_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; 
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_235_ = stack[0].m_obj;
lean_object* v___f_236_ = stack[1].m_obj;
lean_object* v_x_237_ = stack[2].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_235_, v___f_236_, v_x_237_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(lean_object* v___x_269_, lean_object* v___f_270_, lean_object* v_x_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_269_, v___f_270_, v_x_271_);
return v_res_273_;
}
}
lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(lean_object* v___f_274_, lean_object* v_action_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = 0;
lean_inc_ref(v___y_276_);
v___x_280_ = lean_apply_2(v_action_275_, v___y_276_, lean_box(0));
v___x_281_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_278_, v___x_279_, v___x_280_, v___f_274_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_274_ = stack[0].m_obj;
lean_object* v_action_275_ = stack[1].m_obj;
lean_object* v___y_276_ = stack[2].m_obj;
lean_object* v_res_282_;
v_res_282_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_274_, v_action_275_, v___y_276_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(lean_object* v___f_283_, lean_object* v_action_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(v___f_283_, v_action_284_, v___y_285_);
lean_dec_ref(v___y_285_);
return v_res_287_;
}
}
lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(lean_object* v___f_294_, lean_object* v_action_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = 0;
v___x_300_ = lean_apply_1(v_action_295_, lean_box(0));
v___x_301_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_298_, v___x_299_, v___x_300_, v___f_294_);
return v___x_301_;
}
}
LEAN_EXPORT void l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_294_ = stack[0].m_obj;
lean_object* v_action_295_ = stack[1].m_obj;
lean_object* v___y_296_ = stack[2].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_294_, v_action_295_, v___y_296_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(lean_object* v___f_303_, lean_object* v_action_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(v___f_303_, v_action_304_, v___y_305_);
lean_dec_ref(v___y_305_);
return v_res_307_;
}
}
lean_object* l_Std_Http_Request_Builder_empty(lean_object* v_builder_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_box(0);
v___x_314_ = l_Std_Http_Request_Builder_body___redArg(v_builder_311_, v___x_313_);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_empty_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_311_ = stack[0].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Std_Http_Request_Builder_empty(v_builder_311_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty___boxed(lean_object* v_builder_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Http_Request_Builder_empty(v_builder_318_);
lean_dec_ref(v_builder_318_);
return v_res_320_;
}
}
lean_object* l_Std_Http_Response_Builder_empty(lean_object* v_builder_321_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_box(0);
v___x_324_ = l_Std_Http_Response_Builder_body___redArg(v_builder_321_, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Std_Http_Response_Builder_empty_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_321_ = stack[0].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Std_Http_Response_Builder_empty(v_builder_321_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty___boxed(lean_object* v_builder_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Http_Response_Builder_empty(v_builder_328_);
lean_dec_ref(v_builder_328_);
return v_res_330_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Response(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Any(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
