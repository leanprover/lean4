// Lean compiler output
// Module: Std.Async.Signal
// Imports: public import Std.Time public import Std.Internal.UV.Signal public import Std.Async.Select
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_signal_cancel(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sighup"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__0 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__0_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__0_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__1 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__1_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigint"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__2 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__2_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__2_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__3 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__3_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigquit"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__4 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__4_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__4_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__5 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__5_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigtrap"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__6 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__6_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__6_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__7 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__7_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigabrt"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__8 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__8_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__8_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__9 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__9_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigusr1"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__10 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__10_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__10_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__11 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__11_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigusr2"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__12 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__12_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__12_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__13 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__13_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigalrm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__14 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__14_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__14_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__15 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__15_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigterm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__16 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__16_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__16_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__17 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__17_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigchld"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__18 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__18_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__18_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__19 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__19_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigcont"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__20 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__20_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__20_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__21 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__21_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigtstp"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__22 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__22_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__22_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__23 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__23_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigttin"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__24 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__24_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__24_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__25 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__25_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigttou"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__26 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__26_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__26_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__27 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__27_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigurg"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__28 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__28_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__28_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__29 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__29_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigxcpu"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__30 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__30_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__30_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__31 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__31_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigxfsz"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__32 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__32_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__32_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__33 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__33_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Async.Signal.sigvtalrm"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__34 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__34_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__34_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__35 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__35_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Async.Signal.sigprof"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__36 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__36_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__36_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__37 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__37_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Async.Signal.sigwinch"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__38 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__38_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__38_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__39 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__39_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Std.Async.Signal.sigio"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__40 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__40_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__40_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__41 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__41_value;
static const lean_string_object l_Std_Async_instReprSignal_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Async.Signal.sigsys"};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__42 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__42_value;
static const lean_ctor_object l_Std_Async_instReprSignal_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_instReprSignal_repr___closed__42_value)}};
static const lean_object* l_Std_Async_instReprSignal_repr___closed__43 = (const lean_object*)&l_Std_Async_instReprSignal_repr___closed__43_value;
static lean_once_cell_t l_Std_Async_instReprSignal_repr___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_instReprSignal_repr___closed__44;
static lean_once_cell_t l_Std_Async_instReprSignal_repr___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_instReprSignal_repr___closed__45;
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instReprSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instReprSignal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instReprSignal___closed__0 = (const lean_object*)&l_Std_Async_instReprSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_instReprSignal = (const lean_object*)&l_Std_Async_instReprSignal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Async_Signal_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_instDecidableEqSignal(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_instBEqSignal_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_instBEqSignal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_instBEqSignal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_instBEqSignal___closed__0 = (const lean_object*)&l_Std_Async_instBEqSignal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_instBEqSignal = (const lean_object*)&l_Std_Async_instBEqSignal___closed__0_value;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20;
static lean_once_cell_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21;
LEAN_EXPORT uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Signal_Waiter_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Async_Signal_Waiter_wait___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__0_value;
static const lean_closure_object l_Std_Async_Signal_Waiter_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__0_value)} };
static const lean_object* l_Std_Async_Signal_Waiter_wait___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__1_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__2 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__2_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__3 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__3_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___closed__4 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Async_Signal_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Async_Signal_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Async_Signal_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object* v_sighup_22_){
_start:
{
lean_inc(v_sighup_22_);
return v_sighup_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object* v_sighup_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_23_);
lean_dec(v_sighup_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_sighup_28_){
_start:
{
lean_inc(v_sighup_28_);
return v_sighup_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_sighup_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Async_Signal_sighup_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_sighup_32_);
lean_dec(v_sighup_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object* v_sigint_35_){
_start:
{
lean_inc(v_sigint_35_);
return v_sigint_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object* v_sigint_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_36_);
lean_dec(v_sigint_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_sigint_41_){
_start:
{
lean_inc(v_sigint_41_);
return v_sigint_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_sigint_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Async_Signal_sigint_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_sigint_45_);
lean_dec(v_sigint_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object* v_sigquit_48_){
_start:
{
lean_inc(v_sigquit_48_);
return v_sigquit_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object* v_sigquit_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_49_);
lean_dec(v_sigquit_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_sigquit_54_){
_start:
{
lean_inc(v_sigquit_54_);
return v_sigquit_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_sigquit_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Async_Signal_sigquit_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_sigquit_58_);
lean_dec(v_sigquit_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object* v_sigtrap_61_){
_start:
{
lean_inc(v_sigtrap_61_);
return v_sigtrap_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* v_sigtrap_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_62_);
lean_dec(v_sigtrap_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_sigtrap_67_){
_start:
{
lean_inc(v_sigtrap_67_);
return v_sigtrap_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_sigtrap_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Std_Async_Signal_sigtrap_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_sigtrap_71_);
lean_dec(v_sigtrap_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object* v_sigabrt_74_){
_start:
{
lean_inc(v_sigabrt_74_);
return v_sigabrt_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* v_sigabrt_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_75_);
lean_dec(v_sigabrt_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_sigabrt_80_){
_start:
{
lean_inc(v_sigabrt_80_);
return v_sigabrt_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_sigabrt_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Std_Async_Signal_sigabrt_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_sigabrt_84_);
lean_dec(v_sigabrt_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object* v_sigusr1_87_){
_start:
{
lean_inc(v_sigusr1_87_);
return v_sigusr1_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* v_sigusr1_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_88_);
lean_dec(v_sigusr1_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_sigusr1_93_){
_start:
{
lean_inc(v_sigusr1_93_);
return v_sigusr1_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_sigusr1_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Std_Async_Signal_sigusr1_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_sigusr1_97_);
lean_dec(v_sigusr1_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object* v_sigusr2_100_){
_start:
{
lean_inc(v_sigusr2_100_);
return v_sigusr2_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* v_sigusr2_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_101_);
lean_dec(v_sigusr2_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object* v_motive_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_sigusr2_106_){
_start:
{
lean_inc(v_sigusr2_106_);
return v_sigusr2_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_sigusr2_110_){
_start:
{
uint8_t v_t_boxed_111_; lean_object* v_res_112_; 
v_t_boxed_111_ = lean_unbox(v_t_108_);
v_res_112_ = l_Std_Async_Signal_sigusr2_elim(v_motive_107_, v_t_boxed_111_, v_h_109_, v_sigusr2_110_);
lean_dec(v_sigusr2_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object* v_sigalrm_113_){
_start:
{
lean_inc(v_sigalrm_113_);
return v_sigalrm_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* v_sigalrm_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_114_);
lean_dec(v_sigalrm_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object* v_motive_116_, uint8_t v_t_117_, lean_object* v_h_118_, lean_object* v_sigalrm_119_){
_start:
{
lean_inc(v_sigalrm_119_);
return v_sigalrm_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_sigalrm_123_){
_start:
{
uint8_t v_t_boxed_124_; lean_object* v_res_125_; 
v_t_boxed_124_ = lean_unbox(v_t_121_);
v_res_125_ = l_Std_Async_Signal_sigalrm_elim(v_motive_120_, v_t_boxed_124_, v_h_122_, v_sigalrm_123_);
lean_dec(v_sigalrm_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object* v_sigterm_126_){
_start:
{
lean_inc(v_sigterm_126_);
return v_sigterm_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object* v_sigterm_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_127_);
lean_dec(v_sigterm_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim(lean_object* v_motive_129_, uint8_t v_t_130_, lean_object* v_h_131_, lean_object* v_sigterm_132_){
_start:
{
lean_inc(v_sigterm_132_);
return v_sigterm_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_sigterm_136_){
_start:
{
uint8_t v_t_boxed_137_; lean_object* v_res_138_; 
v_t_boxed_137_ = lean_unbox(v_t_134_);
v_res_138_ = l_Std_Async_Signal_sigterm_elim(v_motive_133_, v_t_boxed_137_, v_h_135_, v_sigterm_136_);
lean_dec(v_sigterm_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object* v_sigchld_139_){
_start:
{
lean_inc(v_sigchld_139_);
return v_sigchld_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object* v_sigchld_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_140_);
lean_dec(v_sigchld_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim(lean_object* v_motive_142_, uint8_t v_t_143_, lean_object* v_h_144_, lean_object* v_sigchld_145_){
_start:
{
lean_inc(v_sigchld_145_);
return v_sigchld_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_sigchld_149_){
_start:
{
uint8_t v_t_boxed_150_; lean_object* v_res_151_; 
v_t_boxed_150_ = lean_unbox(v_t_147_);
v_res_151_ = l_Std_Async_Signal_sigchld_elim(v_motive_146_, v_t_boxed_150_, v_h_148_, v_sigchld_149_);
lean_dec(v_sigchld_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object* v_sigcont_152_){
_start:
{
lean_inc(v_sigcont_152_);
return v_sigcont_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object* v_sigcont_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_153_);
lean_dec(v_sigcont_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim(lean_object* v_motive_155_, uint8_t v_t_156_, lean_object* v_h_157_, lean_object* v_sigcont_158_){
_start:
{
lean_inc(v_sigcont_158_);
return v_sigcont_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_sigcont_162_){
_start:
{
uint8_t v_t_boxed_163_; lean_object* v_res_164_; 
v_t_boxed_163_ = lean_unbox(v_t_160_);
v_res_164_ = l_Std_Async_Signal_sigcont_elim(v_motive_159_, v_t_boxed_163_, v_h_161_, v_sigcont_162_);
lean_dec(v_sigcont_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object* v_sigtstp_165_){
_start:
{
lean_inc(v_sigtstp_165_);
return v_sigtstp_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* v_sigtstp_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_166_);
lean_dec(v_sigtstp_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object* v_motive_168_, uint8_t v_t_169_, lean_object* v_h_170_, lean_object* v_sigtstp_171_){
_start:
{
lean_inc(v_sigtstp_171_);
return v_sigtstp_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_sigtstp_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Std_Async_Signal_sigtstp_elim(v_motive_172_, v_t_boxed_176_, v_h_174_, v_sigtstp_175_);
lean_dec(v_sigtstp_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object* v_sigttin_178_){
_start:
{
lean_inc(v_sigttin_178_);
return v_sigttin_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object* v_sigttin_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_179_);
lean_dec(v_sigttin_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_sigttin_184_){
_start:
{
lean_inc(v_sigttin_184_);
return v_sigttin_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_sigttin_188_){
_start:
{
uint8_t v_t_boxed_189_; lean_object* v_res_190_; 
v_t_boxed_189_ = lean_unbox(v_t_186_);
v_res_190_ = l_Std_Async_Signal_sigttin_elim(v_motive_185_, v_t_boxed_189_, v_h_187_, v_sigttin_188_);
lean_dec(v_sigttin_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object* v_sigttou_191_){
_start:
{
lean_inc(v_sigttou_191_);
return v_sigttou_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object* v_sigttou_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_192_);
lean_dec(v_sigttou_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim(lean_object* v_motive_194_, uint8_t v_t_195_, lean_object* v_h_196_, lean_object* v_sigttou_197_){
_start:
{
lean_inc(v_sigttou_197_);
return v_sigttou_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_sigttou_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Std_Async_Signal_sigttou_elim(v_motive_198_, v_t_boxed_202_, v_h_200_, v_sigttou_201_);
lean_dec(v_sigttou_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object* v_sigurg_204_){
_start:
{
lean_inc(v_sigurg_204_);
return v_sigurg_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object* v_sigurg_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_205_);
lean_dec(v_sigurg_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_sigurg_210_){
_start:
{
lean_inc(v_sigurg_210_);
return v_sigurg_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_sigurg_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Std_Async_Signal_sigurg_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_sigurg_214_);
lean_dec(v_sigurg_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object* v_sigxcpu_217_){
_start:
{
lean_inc(v_sigxcpu_217_);
return v_sigxcpu_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* v_sigxcpu_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_218_);
lean_dec(v_sigxcpu_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_sigxcpu_223_){
_start:
{
lean_inc(v_sigxcpu_223_);
return v_sigxcpu_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_sigxcpu_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Std_Async_Signal_sigxcpu_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_sigxcpu_227_);
lean_dec(v_sigxcpu_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object* v_sigxfsz_230_){
_start:
{
lean_inc(v_sigxfsz_230_);
return v_sigxfsz_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* v_sigxfsz_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_231_);
lean_dec(v_sigxfsz_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_sigxfsz_236_){
_start:
{
lean_inc(v_sigxfsz_236_);
return v_sigxfsz_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_sigxfsz_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Std_Async_Signal_sigxfsz_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_sigxfsz_240_);
lean_dec(v_sigxfsz_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object* v_sigvtalrm_243_){
_start:
{
lean_inc(v_sigvtalrm_243_);
return v_sigvtalrm_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* v_sigvtalrm_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_244_);
lean_dec(v_sigvtalrm_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_sigvtalrm_249_){
_start:
{
lean_inc(v_sigvtalrm_249_);
return v_sigvtalrm_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_sigvtalrm_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Std_Async_Signal_sigvtalrm_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_sigvtalrm_253_);
lean_dec(v_sigvtalrm_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg(lean_object* v_sigprof_256_){
_start:
{
lean_inc(v_sigprof_256_);
return v_sigprof_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg___boxed(lean_object* v_sigprof_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Async_Signal_sigprof_elim___redArg(v_sigprof_257_);
lean_dec(v_sigprof_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_sigprof_262_){
_start:
{
lean_inc(v_sigprof_262_);
return v_sigprof_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_sigprof_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Std_Async_Signal_sigprof_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_sigprof_266_);
lean_dec(v_sigprof_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object* v_sigwinch_269_){
_start:
{
lean_inc(v_sigwinch_269_);
return v_sigwinch_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* v_sigwinch_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_270_);
lean_dec(v_sigwinch_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object* v_motive_272_, uint8_t v_t_273_, lean_object* v_h_274_, lean_object* v_sigwinch_275_){
_start:
{
lean_inc(v_sigwinch_275_);
return v_sigwinch_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_sigwinch_279_){
_start:
{
uint8_t v_t_boxed_280_; lean_object* v_res_281_; 
v_t_boxed_280_ = lean_unbox(v_t_277_);
v_res_281_ = l_Std_Async_Signal_sigwinch_elim(v_motive_276_, v_t_boxed_280_, v_h_278_, v_sigwinch_279_);
lean_dec(v_sigwinch_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object* v_sigio_282_){
_start:
{
lean_inc(v_sigio_282_);
return v_sigio_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object* v_sigio_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_283_);
lean_dec(v_sigio_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim(lean_object* v_motive_285_, uint8_t v_t_286_, lean_object* v_h_287_, lean_object* v_sigio_288_){
_start:
{
lean_inc(v_sigio_288_);
return v_sigio_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_sigio_292_){
_start:
{
uint8_t v_t_boxed_293_; lean_object* v_res_294_; 
v_t_boxed_293_ = lean_unbox(v_t_290_);
v_res_294_ = l_Std_Async_Signal_sigio_elim(v_motive_289_, v_t_boxed_293_, v_h_291_, v_sigio_292_);
lean_dec(v_sigio_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object* v_sigsys_295_){
_start:
{
lean_inc(v_sigsys_295_);
return v_sigsys_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object* v_sigsys_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_296_);
lean_dec(v_sigsys_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim(lean_object* v_motive_298_, uint8_t v_t_299_, lean_object* v_h_300_, lean_object* v_sigsys_301_){
_start:
{
lean_inc(v_sigsys_301_);
return v_sigsys_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_sigsys_305_){
_start:
{
uint8_t v_t_boxed_306_; lean_object* v_res_307_; 
v_t_boxed_306_ = lean_unbox(v_t_303_);
v_res_307_ = l_Std_Async_Signal_sigsys_elim(v_motive_302_, v_t_boxed_306_, v_h_304_, v_sigsys_305_);
lean_dec(v_sigsys_305_);
return v_res_307_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__44(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(2u);
v___x_375_ = lean_nat_to_int(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__45(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_to_int(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr(uint8_t v_x_378_, lean_object* v_prec_379_){
_start:
{
lean_object* v___y_381_; lean_object* v___y_388_; lean_object* v___y_395_; lean_object* v___y_402_; lean_object* v___y_409_; lean_object* v___y_416_; lean_object* v___y_423_; lean_object* v___y_430_; lean_object* v___y_437_; lean_object* v___y_444_; lean_object* v___y_451_; lean_object* v___y_458_; lean_object* v___y_465_; lean_object* v___y_472_; lean_object* v___y_479_; lean_object* v___y_486_; lean_object* v___y_493_; lean_object* v___y_500_; lean_object* v___y_507_; lean_object* v___y_514_; lean_object* v___y_521_; lean_object* v___y_528_; 
switch(v_x_378_)
{
case 0:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1024u);
v___x_535_ = lean_nat_dec_le(v___x_534_, v_prec_379_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_381_ = v___x_536_;
goto v___jp_380_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_381_ = v___x_537_;
goto v___jp_380_;
}
}
case 1:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1024u);
v___x_539_ = lean_nat_dec_le(v___x_538_, v_prec_379_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_388_ = v___x_540_;
goto v___jp_387_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_388_ = v___x_541_;
goto v___jp_387_;
}
}
case 2:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1024u);
v___x_543_ = lean_nat_dec_le(v___x_542_, v_prec_379_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_395_ = v___x_544_;
goto v___jp_394_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_395_ = v___x_545_;
goto v___jp_394_;
}
}
case 3:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(1024u);
v___x_547_ = lean_nat_dec_le(v___x_546_, v_prec_379_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_402_ = v___x_548_;
goto v___jp_401_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_402_ = v___x_549_;
goto v___jp_401_;
}
}
case 4:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(1024u);
v___x_551_ = lean_nat_dec_le(v___x_550_, v_prec_379_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_409_ = v___x_552_;
goto v___jp_408_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_409_ = v___x_553_;
goto v___jp_408_;
}
}
case 5:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1024u);
v___x_555_ = lean_nat_dec_le(v___x_554_, v_prec_379_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_416_ = v___x_556_;
goto v___jp_415_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_416_ = v___x_557_;
goto v___jp_415_;
}
}
case 6:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1024u);
v___x_559_ = lean_nat_dec_le(v___x_558_, v_prec_379_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_423_ = v___x_560_;
goto v___jp_422_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_423_ = v___x_561_;
goto v___jp_422_;
}
}
case 7:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1024u);
v___x_563_ = lean_nat_dec_le(v___x_562_, v_prec_379_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_430_ = v___x_564_;
goto v___jp_429_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_430_ = v___x_565_;
goto v___jp_429_;
}
}
case 8:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(1024u);
v___x_567_ = lean_nat_dec_le(v___x_566_, v_prec_379_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_437_ = v___x_568_;
goto v___jp_436_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_437_ = v___x_569_;
goto v___jp_436_;
}
}
case 9:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1024u);
v___x_571_ = lean_nat_dec_le(v___x_570_, v_prec_379_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_444_ = v___x_572_;
goto v___jp_443_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_444_ = v___x_573_;
goto v___jp_443_;
}
}
case 10:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_379_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_451_ = v___x_576_;
goto v___jp_450_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_451_ = v___x_577_;
goto v___jp_450_;
}
}
case 11:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1024u);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_prec_379_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_458_ = v___x_580_;
goto v___jp_457_;
}
else
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_458_ = v___x_581_;
goto v___jp_457_;
}
}
case 12:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_379_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_465_ = v___x_584_;
goto v___jp_464_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_465_ = v___x_585_;
goto v___jp_464_;
}
}
case 13:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_379_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_472_ = v___x_588_;
goto v___jp_471_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_472_ = v___x_589_;
goto v___jp_471_;
}
}
case 14:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_379_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_479_ = v___x_592_;
goto v___jp_478_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_479_ = v___x_593_;
goto v___jp_478_;
}
}
case 15:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_595_ = lean_nat_dec_le(v___x_594_, v_prec_379_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_486_ = v___x_596_;
goto v___jp_485_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_486_ = v___x_597_;
goto v___jp_485_;
}
}
case 16:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_599_ = lean_nat_dec_le(v___x_598_, v_prec_379_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_493_ = v___x_600_;
goto v___jp_492_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_493_ = v___x_601_;
goto v___jp_492_;
}
}
case 17:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1024u);
v___x_603_ = lean_nat_dec_le(v___x_602_, v_prec_379_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_500_ = v___x_604_;
goto v___jp_499_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_500_ = v___x_605_;
goto v___jp_499_;
}
}
case 18:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1024u);
v___x_607_ = lean_nat_dec_le(v___x_606_, v_prec_379_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_507_ = v___x_608_;
goto v___jp_506_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_507_ = v___x_609_;
goto v___jp_506_;
}
}
case 19:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_611_ = lean_nat_dec_le(v___x_610_, v_prec_379_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_514_ = v___x_612_;
goto v___jp_513_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_514_ = v___x_613_;
goto v___jp_513_;
}
}
case 20:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1024u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_379_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_521_ = v___x_616_;
goto v___jp_520_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_521_ = v___x_617_;
goto v___jp_520_;
}
}
default: 
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_379_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_528_ = v___x_620_;
goto v___jp_527_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_528_ = v___x_621_;
goto v___jp_527_;
}
}
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_382_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__1));
lean_inc(v___y_381_);
v___x_383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_383_, 0, v___y_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = 0;
v___x_385_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*1, v___x_384_);
v___x_386_ = l_Repr_addAppParen(v___x_385_, v_prec_379_);
return v___x_386_;
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_389_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__3));
lean_inc(v___y_388_);
v___x_390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_390_, 0, v___y_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = 0;
v___x_392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_391_);
v___x_393_ = l_Repr_addAppParen(v___x_392_, v_prec_379_);
return v___x_393_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_396_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__5));
lean_inc(v___y_395_);
v___x_397_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_397_, 0, v___y_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = 0;
v___x_399_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_398_);
v___x_400_ = l_Repr_addAppParen(v___x_399_, v_prec_379_);
return v___x_400_;
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__7));
lean_inc(v___y_402_);
v___x_404_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_404_, 0, v___y_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = 0;
v___x_406_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*1, v___x_405_);
v___x_407_ = l_Repr_addAppParen(v___x_406_, v_prec_379_);
return v___x_407_;
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_410_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__9));
lean_inc(v___y_409_);
v___x_411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_411_, 0, v___y_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = 0;
v___x_413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_412_);
v___x_414_ = l_Repr_addAppParen(v___x_413_, v_prec_379_);
return v___x_414_;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_417_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__11));
lean_inc(v___y_416_);
v___x_418_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_418_, 0, v___y_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = 0;
v___x_420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = l_Repr_addAppParen(v___x_420_, v_prec_379_);
return v___x_421_;
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_424_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__13));
lean_inc(v___y_423_);
v___x_425_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_425_, 0, v___y_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = 0;
v___x_427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v___x_426_);
v___x_428_ = l_Repr_addAppParen(v___x_427_, v_prec_379_);
return v___x_428_;
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_431_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__15));
lean_inc(v___y_430_);
v___x_432_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_432_, 0, v___y_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = 0;
v___x_434_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
v___x_435_ = l_Repr_addAppParen(v___x_434_, v_prec_379_);
return v___x_435_;
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_438_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__17));
lean_inc(v___y_437_);
v___x_439_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_439_, 0, v___y_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = 0;
v___x_441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___x_440_);
v___x_442_ = l_Repr_addAppParen(v___x_441_, v_prec_379_);
return v___x_442_;
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__19));
lean_inc(v___y_444_);
v___x_446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_446_, 0, v___y_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = 0;
v___x_448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___x_447_);
v___x_449_ = l_Repr_addAppParen(v___x_448_, v_prec_379_);
return v___x_449_;
}
v___jp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_452_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__21));
lean_inc(v___y_451_);
v___x_453_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_453_, 0, v___y_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = 0;
v___x_455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*1, v___x_454_);
v___x_456_ = l_Repr_addAppParen(v___x_455_, v_prec_379_);
return v___x_456_;
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__23));
lean_inc(v___y_458_);
v___x_460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_460_, 0, v___y_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = 0;
v___x_462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_461_);
v___x_463_ = l_Repr_addAppParen(v___x_462_, v_prec_379_);
return v___x_463_;
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__25));
lean_inc(v___y_465_);
v___x_467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_467_, 0, v___y_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = 0;
v___x_469_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*1, v___x_468_);
v___x_470_ = l_Repr_addAppParen(v___x_469_, v_prec_379_);
return v___x_470_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_473_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__27));
lean_inc(v___y_472_);
v___x_474_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = 0;
v___x_476_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*1, v___x_475_);
v___x_477_ = l_Repr_addAppParen(v___x_476_, v_prec_379_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__29));
lean_inc(v___y_479_);
v___x_481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_481_, 0, v___y_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = 0;
v___x_483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*1, v___x_482_);
v___x_484_ = l_Repr_addAppParen(v___x_483_, v_prec_379_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__31));
lean_inc(v___y_486_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___y_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = 0;
v___x_490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1, v___x_489_);
v___x_491_ = l_Repr_addAppParen(v___x_490_, v_prec_379_);
return v___x_491_;
}
v___jp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__33));
lean_inc(v___y_493_);
v___x_495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = 0;
v___x_497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*1, v___x_496_);
v___x_498_ = l_Repr_addAppParen(v___x_497_, v_prec_379_);
return v___x_498_;
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_501_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__35));
lean_inc(v___y_500_);
v___x_502_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_502_, 0, v___y_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = 0;
v___x_504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_503_);
v___x_505_ = l_Repr_addAppParen(v___x_504_, v_prec_379_);
return v___x_505_;
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__37));
lean_inc(v___y_507_);
v___x_509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_509_, 0, v___y_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = 0;
v___x_511_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_510_);
v___x_512_ = l_Repr_addAppParen(v___x_511_, v_prec_379_);
return v___x_512_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_515_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__39));
lean_inc(v___y_514_);
v___x_516_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_516_, 0, v___y_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = 0;
v___x_518_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*1, v___x_517_);
v___x_519_ = l_Repr_addAppParen(v___x_518_, v_prec_379_);
return v___x_519_;
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__41));
lean_inc(v___y_521_);
v___x_523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_523_, 0, v___y_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = 0;
v___x_525_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_524_);
v___x_526_ = l_Repr_addAppParen(v___x_525_, v_prec_379_);
return v___x_526_;
}
v___jp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_529_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__43));
lean_inc(v___y_528_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = 0;
v___x_532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_531_);
v___x_533_ = l_Repr_addAppParen(v___x_532_, v_prec_379_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object* v_x_622_, lean_object* v_prec_623_){
_start:
{
uint8_t v_x_1197__boxed_624_; lean_object* v_res_625_; 
v_x_1197__boxed_624_ = lean_unbox(v_x_622_);
v_res_625_ = l_Std_Async_instReprSignal_repr(v_x_1197__boxed_624_, v_prec_623_);
lean_dec(v_prec_623_);
return v_res_625_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Signal_ofNat(lean_object* v_n_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(10u);
v___x_630_ = lean_nat_dec_le(v_n_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(15u);
v___x_632_ = lean_nat_dec_le(v_n_628_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(18u);
v___x_634_ = lean_nat_dec_le(v_n_628_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(19u);
v___x_636_ = lean_nat_dec_le(v_n_628_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(20u);
v___x_638_ = lean_nat_dec_le(v_n_628_, v___x_637_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = 21;
return v___x_639_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = 20;
return v___x_640_;
}
}
else
{
uint8_t v___x_641_; 
v___x_641_ = 19;
return v___x_641_;
}
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(16u);
v___x_643_ = lean_nat_dec_le(v_n_628_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(17u);
v___x_645_ = lean_nat_dec_le(v_n_628_, v___x_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = 18;
return v___x_646_;
}
else
{
uint8_t v___x_647_; 
v___x_647_ = 17;
return v___x_647_;
}
}
else
{
uint8_t v___x_648_; 
v___x_648_ = 16;
return v___x_648_;
}
}
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(12u);
v___x_650_ = lean_nat_dec_le(v_n_628_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(13u);
v___x_652_ = lean_nat_dec_le(v_n_628_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(14u);
v___x_654_ = lean_nat_dec_le(v_n_628_, v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 15;
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 14;
return v___x_656_;
}
}
else
{
uint8_t v___x_657_; 
v___x_657_ = 13;
return v___x_657_;
}
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(11u);
v___x_659_ = lean_nat_dec_le(v_n_628_, v___x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 12;
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 11;
return v___x_661_;
}
}
}
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(4u);
v___x_663_ = lean_nat_dec_le(v_n_628_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(7u);
v___x_665_ = lean_nat_dec_le(v_n_628_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(8u);
v___x_667_ = lean_nat_dec_le(v_n_628_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(9u);
v___x_669_ = lean_nat_dec_le(v_n_628_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 10;
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = 9;
return v___x_671_;
}
}
else
{
uint8_t v___x_672_; 
v___x_672_ = 8;
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(5u);
v___x_674_ = lean_nat_dec_le(v_n_628_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(6u);
v___x_676_ = lean_nat_dec_le(v_n_628_, v___x_675_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 7;
return v___x_677_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 6;
return v___x_678_;
}
}
else
{
uint8_t v___x_679_; 
v___x_679_ = 5;
return v___x_679_;
}
}
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_dec_le(v_n_628_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = lean_nat_dec_le(v_n_628_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_unsigned_to_nat(3u);
v___x_685_ = lean_nat_dec_le(v_n_628_, v___x_684_);
if (v___x_685_ == 0)
{
uint8_t v___x_686_; 
v___x_686_ = 4;
return v___x_686_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = 3;
return v___x_687_;
}
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 2;
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_nat_dec_le(v_n_628_, v___x_689_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = 1;
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object* v_n_693_){
_start:
{
uint8_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Std_Async_Signal_ofNat(v_n_693_);
lean_dec(v_n_693_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instDecidableEqSignal(uint8_t v_x_696_, uint8_t v_y_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_698_ = lean_box(v_x_696_);
v___x_699_ = lean_obj_tag_nat(v___x_698_);
lean_dec(v___x_698_);
v___x_700_ = lean_box(v_y_697_);
v___x_701_ = lean_obj_tag_nat(v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = lean_nat_dec_eq(v___x_699_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object* v_x_703_, lean_object* v_y_704_){
_start:
{
uint8_t v_x_23__boxed_705_; uint8_t v_y_24__boxed_706_; uint8_t v_res_707_; lean_object* v_r_708_; 
v_x_23__boxed_705_ = lean_unbox(v_x_703_);
v_y_24__boxed_706_ = lean_unbox(v_y_704_);
v_res_707_ = l_Std_Async_instDecidableEqSignal(v_x_23__boxed_705_, v_y_24__boxed_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instBEqSignal_beq(uint8_t v_x_709_, uint8_t v_y_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_711_ = lean_box(v_x_709_);
v___x_712_ = lean_obj_tag_nat(v___x_711_);
lean_dec(v___x_711_);
v___x_713_ = lean_box(v_y_710_);
v___x_714_ = lean_obj_tag_nat(v___x_713_);
lean_dec(v___x_713_);
v___x_715_ = lean_nat_dec_eq(v___x_712_, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object* v_x_716_, lean_object* v_y_717_){
_start:
{
uint8_t v_x_24__boxed_718_; uint8_t v_y_25__boxed_719_; uint8_t v_res_720_; lean_object* v_r_721_; 
v_x_24__boxed_718_ = lean_unbox(v_x_716_);
v_y_25__boxed_719_ = lean_unbox(v_y_717_);
v_res_720_ = l_Std_Async_instBEqSignal_beq(v_x_24__boxed_718_, v_y_25__boxed_719_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0(void){
_start:
{
lean_object* v___x_724_; uint32_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_int32_of_nat(v___x_724_);
return v___x_725_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1(void){
_start:
{
lean_object* v___x_726_; uint32_t v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_int32_of_nat(v___x_726_);
return v___x_727_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2(void){
_start:
{
lean_object* v___x_728_; uint32_t v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(3u);
v___x_729_ = lean_int32_of_nat(v___x_728_);
return v___x_729_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3(void){
_start:
{
lean_object* v___x_730_; uint32_t v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(5u);
v___x_731_ = lean_int32_of_nat(v___x_730_);
return v___x_731_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4(void){
_start:
{
lean_object* v___x_732_; uint32_t v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(6u);
v___x_733_ = lean_int32_of_nat(v___x_732_);
return v___x_733_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5(void){
_start:
{
lean_object* v___x_734_; uint32_t v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(10u);
v___x_735_ = lean_int32_of_nat(v___x_734_);
return v___x_735_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6(void){
_start:
{
lean_object* v___x_736_; uint32_t v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(12u);
v___x_737_ = lean_int32_of_nat(v___x_736_);
return v___x_737_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7(void){
_start:
{
lean_object* v___x_738_; uint32_t v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(14u);
v___x_739_ = lean_int32_of_nat(v___x_738_);
return v___x_739_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8(void){
_start:
{
lean_object* v___x_740_; uint32_t v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(15u);
v___x_741_ = lean_int32_of_nat(v___x_740_);
return v___x_741_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9(void){
_start:
{
lean_object* v___x_742_; uint32_t v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(17u);
v___x_743_ = lean_int32_of_nat(v___x_742_);
return v___x_743_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10(void){
_start:
{
lean_object* v___x_744_; uint32_t v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(18u);
v___x_745_ = lean_int32_of_nat(v___x_744_);
return v___x_745_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11(void){
_start:
{
lean_object* v___x_746_; uint32_t v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(20u);
v___x_747_ = lean_int32_of_nat(v___x_746_);
return v___x_747_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12(void){
_start:
{
lean_object* v___x_748_; uint32_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(21u);
v___x_749_ = lean_int32_of_nat(v___x_748_);
return v___x_749_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13(void){
_start:
{
lean_object* v___x_750_; uint32_t v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(22u);
v___x_751_ = lean_int32_of_nat(v___x_750_);
return v___x_751_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14(void){
_start:
{
lean_object* v___x_752_; uint32_t v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(23u);
v___x_753_ = lean_int32_of_nat(v___x_752_);
return v___x_753_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15(void){
_start:
{
lean_object* v___x_754_; uint32_t v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(24u);
v___x_755_ = lean_int32_of_nat(v___x_754_);
return v___x_755_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16(void){
_start:
{
lean_object* v___x_756_; uint32_t v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(25u);
v___x_757_ = lean_int32_of_nat(v___x_756_);
return v___x_757_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17(void){
_start:
{
lean_object* v___x_758_; uint32_t v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(26u);
v___x_759_ = lean_int32_of_nat(v___x_758_);
return v___x_759_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18(void){
_start:
{
lean_object* v___x_760_; uint32_t v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(27u);
v___x_761_ = lean_int32_of_nat(v___x_760_);
return v___x_761_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19(void){
_start:
{
lean_object* v___x_762_; uint32_t v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(28u);
v___x_763_ = lean_int32_of_nat(v___x_762_);
return v___x_763_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20(void){
_start:
{
lean_object* v___x_764_; uint32_t v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(29u);
v___x_765_ = lean_int32_of_nat(v___x_764_);
return v___x_765_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21(void){
_start:
{
lean_object* v___x_766_; uint32_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(31u);
v___x_767_ = lean_int32_of_nat(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t v_x_768_){
_start:
{
switch(v_x_768_)
{
case 0:
{
uint32_t v___x_769_; 
v___x_769_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0);
return v___x_769_;
}
case 1:
{
uint32_t v___x_770_; 
v___x_770_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1);
return v___x_770_;
}
case 2:
{
uint32_t v___x_771_; 
v___x_771_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2);
return v___x_771_;
}
case 3:
{
uint32_t v___x_772_; 
v___x_772_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3);
return v___x_772_;
}
case 4:
{
uint32_t v___x_773_; 
v___x_773_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4);
return v___x_773_;
}
case 5:
{
uint32_t v___x_774_; 
v___x_774_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5);
return v___x_774_;
}
case 6:
{
uint32_t v___x_775_; 
v___x_775_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6);
return v___x_775_;
}
case 7:
{
uint32_t v___x_776_; 
v___x_776_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7);
return v___x_776_;
}
case 8:
{
uint32_t v___x_777_; 
v___x_777_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8);
return v___x_777_;
}
case 9:
{
uint32_t v___x_778_; 
v___x_778_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9);
return v___x_778_;
}
case 10:
{
uint32_t v___x_779_; 
v___x_779_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10);
return v___x_779_;
}
case 11:
{
uint32_t v___x_780_; 
v___x_780_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11);
return v___x_780_;
}
case 12:
{
uint32_t v___x_781_; 
v___x_781_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12);
return v___x_781_;
}
case 13:
{
uint32_t v___x_782_; 
v___x_782_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13);
return v___x_782_;
}
case 14:
{
uint32_t v___x_783_; 
v___x_783_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14);
return v___x_783_;
}
case 15:
{
uint32_t v___x_784_; 
v___x_784_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15);
return v___x_784_;
}
case 16:
{
uint32_t v___x_785_; 
v___x_785_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16);
return v___x_785_;
}
case 17:
{
uint32_t v___x_786_; 
v___x_786_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17);
return v___x_786_;
}
case 18:
{
uint32_t v___x_787_; 
v___x_787_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18);
return v___x_787_;
}
case 19:
{
uint32_t v___x_788_; 
v___x_788_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19);
return v___x_788_;
}
case 20:
{
uint32_t v___x_789_; 
v___x_789_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20);
return v___x_789_;
}
default: 
{
uint32_t v___x_790_; 
v___x_790_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object* v_x_791_){
_start:
{
uint8_t v_x_356__boxed_792_; uint32_t v_res_793_; lean_object* v_r_794_; 
v_x_356__boxed_792_ = lean_unbox(v_x_791_);
v_res_793_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_792_);
v_r_794_ = lean_box_uint32(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t v_signum_795_, uint8_t v_repeating_796_){
_start:
{
uint32_t v___x_798_; lean_object* v___x_799_; 
v___x_798_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_795_);
v___x_799_ = lean_uv_signal_mk(v___x_798_, v_repeating_796_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_799_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_799_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object* v_signum_816_, lean_object* v_repeating_817_, lean_object* v_a_818_){
_start:
{
uint8_t v_signum_boxed_819_; uint8_t v_repeating_boxed_820_; lean_object* v_res_821_; 
v_signum_boxed_819_ = lean_unbox(v_signum_816_);
v_repeating_boxed_820_ = lean_unbox(v_repeating_817_);
v_res_821_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_819_, v_repeating_boxed_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object* v___x_822_, lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_mk_io_user_error(v___x_822_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v___x_822_);
v_val_826_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v_x_823_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_dec(v_x_823_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_val_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait(lean_object* v_s_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_uv_signal_next(v_s_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___f_844_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_845_ = lean_io_promise_result_opt(v_a_840_);
lean_dec(v_a_840_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = 1;
v___x_848_ = lean_task_map(v___f_844_, v___x_845_, v___x_846_, v___x_847_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_839_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_839_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object* v_s_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_Async_Signal_Waiter_wait(v_s_861_);
lean_dec(v_s_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop(lean_object* v_s_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_uv_signal_stop(v_s_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object* v_s_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_Async_Signal_Waiter_stop(v_s_867_);
lean_dec(v_s_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object* v_w_872_, lean_object* v_lose_873_){
_start:
{
lean_object* v_finished_875_; lean_object* v_promise_876_; lean_object* v___x_877_; uint8_t v___y_879_; uint8_t v___x_887_; 
v_finished_875_ = lean_ctor_get(v_w_872_, 0);
v_promise_876_ = lean_ctor_get(v_w_872_, 1);
v___x_877_ = lean_st_ref_take(v_finished_875_);
v___x_887_ = lean_unbox(v___x_877_);
lean_dec(v___x_877_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; 
v___x_888_ = 1;
v___y_879_ = v___x_888_;
goto v___jp_878_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = 0;
v___y_879_ = v___x_889_;
goto v___jp_878_;
}
v___jp_878_:
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = 1;
v___x_881_ = lean_box(v___x_880_);
v___x_882_ = lean_st_ref_put(v_finished_875_, v___x_881_);
if (v___y_879_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_apply_1(v_lose_873_, lean_box(0));
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v_lose_873_);
v___x_884_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0));
v___x_885_ = lean_io_promise_resolve(v___x_884_, v_promise_876_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* v_w_890_, lean_object* v_lose_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_w_890_, v_lose_891_);
lean_dec_ref(v_w_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_914_; 
v_a_906_ = lean_ctor_get(v_x_904_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_914_ == 0)
{
v___x_908_ = v_x_904_;
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v_x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; uint8_t v___x_916_; 
v_a_915_ = lean_ctor_get(v_x_904_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v_x_904_, 1);
v___x_916_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__0___closed__1));
return v___x_917_;
}
else
{
lean_object* v___x_918_; 
v___x_918_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__0___closed__4));
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* v_x_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_x_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object* v___x_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* v___x_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Async_Signal_Waiter_selector___lam__1(v___x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object* v_waiter_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_a_934_; 
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v_a_931_, 1);
v_a_934_ = v_a_936_;
goto v___jp_933_;
}
else
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_947_; 
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_a_931_, 0);
lean_dec(v_unused_948_);
v___x_938_ = v_a_931_;
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_a_931_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___f_940_; lean_object* v___x_941_; 
v___f_940_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0));
v___x_941_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_waiter_930_, v___f_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_a_942_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
lean_object* v_a_946_; 
lean_del_object(v___x_938_);
v_a_946_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_941_, 1);
v_a_934_ = v_a_946_;
goto v___jp_933_;
}
}
}
v___jp_933_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_a_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* v_waiter_949_, lean_object* v_a_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Async_Signal_Waiter_selector___lam__2(v_waiter_949_, v_a_950_);
lean_dec_ref(v_waiter_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object* v___f_955_, lean_object* v_x_956_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___f_955_);
v_a_958_ = lean_ctor_get(v_x_956_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x_956_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v_x_956_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v_x_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_967_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v_x_956_, 1);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = 0;
v___x_970_ = lean_io_map_task(v___f_955_, v_a_967_, v___x_968_, v___x_969_);
lean_dec_ref(v___x_970_);
v___x_971_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__3___closed__0));
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3___boxed(lean_object* v___f_972_, lean_object* v_x_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Async_Signal_Waiter_selector___lam__3(v___f_972_, v_x_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object* v_s_976_, lean_object* v_waiter_977_){
_start:
{
lean_object* v___f_979_; lean_object* v___f_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v_val_984_; lean_object* v___x_987_; 
v___f_979_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__2___boxed), 3, 1);
lean_closure_set(v___f_979_, 0, v_waiter_977_);
v___f_980_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_980_, 0, v___f_979_);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = 0;
v___x_987_ = lean_uv_signal_next(v_s_976_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_999_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_999_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___f_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___f_992_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_993_ = lean_io_promise_result_opt(v_a_988_);
lean_dec(v_a_988_);
v___x_994_ = 1;
v___x_995_ = lean_task_map(v___f_992_, v___x_993_, v___x_981_, v___x_994_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v___x_995_);
v___x_997_ = v___x_990_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_val_984_ = v___x_997_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_987_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_987_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 0);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_val_984_ = v___x_1005_;
goto v___jp_983_;
}
}
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_val_984_);
v___x_986_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_981_, v___x_982_, v___x_985_, v___f_980_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* v_s_1008_, lean_object* v_waiter_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_1008_, v_waiter_1009_);
lean_dec(v_s_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object* v_s_1012_){
_start:
{
lean_object* v_val_1015_; lean_object* v___x_1017_; 
v___x_1017_ = lean_uv_signal_cancel(v_s_1012_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v_val_1015_ = v___x_1023_;
goto v___jp_1014_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
v_val_1015_ = v___x_1031_;
goto v___jp_1014_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_val_1015_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* v_s_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_Async_Signal_Waiter_selector___lam__4(v_s_1034_);
lean_dec(v_s_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object* v_a_1037_, lean_object* v___f_1038_, lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___f_1038_);
v_a_1041_ = lean_ctor_get(v_x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_x_1039_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v_x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
else
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1062_; 
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_x_1039_, 0);
lean_dec(v_unused_1063_);
v___x_1051_ = v_x_1039_;
v_isShared_1052_ = v_isSharedCheck_1062_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v_x_1039_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1062_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = 0;
v___x_1055_ = l_IO_Promise_isResolved___redArg(v_a_1037_);
v___x_1056_ = lean_box(v___x_1055_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1056_);
v___x_1058_ = v___x_1051_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1053_, v___x_1054_, v___x_1059_, v___f_1038_);
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* v_a_1064_, lean_object* v___f_1065_, lean_object* v_x_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_Async_Signal_Waiter_selector___lam__6(v_a_1064_, v___f_1065_, v_x_1066_);
lean_dec(v_a_1064_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object* v___f_1069_, lean_object* v_s_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___f_1069_);
v_a_1073_ = lean_ctor_get(v_x_1071_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_x_1071_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v_x_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1102_; 
v_a_1082_ = lean_ctor_get(v_x_1071_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1084_ = v_x_1071_;
v_isShared_1085_ = v_isSharedCheck_1102_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v_x_1071_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1102_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___f_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v_val_1090_; lean_object* v___x_1093_; 
v___f_1086_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1086_, 0, v_a_1082_);
lean_closure_set(v___f_1086_, 1, v___f_1069_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = 0;
v___x_1093_ = lean_uv_signal_cancel(v_s_1070_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v_a_1094_);
v___x_1096_ = v___x_1084_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_val_1090_ = v___x_1096_;
goto v___jp_1089_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; 
v_a_1098_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1093_, 1);
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1098_);
v___x_1100_ = v___x_1084_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v_val_1090_ = v___x_1100_;
goto v___jp_1089_;
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_val_1090_);
v___x_1092_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1087_, v___x_1088_, v___x_1091_, v___f_1086_);
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* v___f_1103_, lean_object* v_s_1104_, lean_object* v_x_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_Async_Signal_Waiter_selector___lam__7(v___f_1103_, v_s_1104_, v_x_1105_);
lean_dec(v_s_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object* v___f_1108_, lean_object* v_s_1109_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v_val_1114_; lean_object* v___x_1117_; 
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = 0;
v___x_1117_ = lean_uv_signal_next(v_s_1109_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v_val_1114_ = v___x_1123_;
goto v___jp_1113_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v_val_1114_ = v___x_1131_;
goto v___jp_1113_;
}
}
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_val_1114_);
v___x_1116_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1111_, v___x_1112_, v___x_1115_, v___f_1108_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* v___f_1134_, lean_object* v_s_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___f_1134_, v_s_1135_);
lean_dec(v_s_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object* v_s_1139_){
_start:
{
lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; 
v___f_1140_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__0));
lean_inc_n(v_s_1139_, 3);
v___f_1141_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1141_, 0, v_s_1139_);
v___f_1142_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1142_, 0, v_s_1139_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1143_, 0, v___f_1140_);
lean_closure_set(v___f_1143_, 1, v_s_1139_);
v___f_1144_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_1144_, 0, v___f_1143_);
lean_closure_set(v___f_1144_, 1, v_s_1139_);
v___x_1145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1145_, 0, v___f_1144_);
lean_ctor_set(v___x_1145_, 1, v___f_1141_);
lean_ctor_set(v___x_1145_, 2, v___f_1142_);
return v___x_1145_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Signal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Signal(builtin);
}
#ifdef __cplusplus
}
#endif
