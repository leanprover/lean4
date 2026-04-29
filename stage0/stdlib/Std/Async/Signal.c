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
lean_object* lean_uv_signal_cancel(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_uv_signal_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uv_signal_stop(lean_object*);
lean_object* lean_uv_signal_mk(uint32_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_Signal_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value;
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___closed__2 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__8___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__0 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__0_value;
static const lean_closure_object l_Std_Async_Signal_Waiter_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Signal_Waiter_selector___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Signal_Waiter_selector___closed__1 = (const lean_object*)&l_Std_Async_Signal_Waiter_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
case 7:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
case 8:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(8u);
return v___x_10_;
}
case 9:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(9u);
return v___x_11_;
}
case 10:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(10u);
return v___x_12_;
}
case 11:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(11u);
return v___x_13_;
}
case 12:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(12u);
return v___x_14_;
}
case 13:
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(13u);
return v___x_15_;
}
case 14:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(14u);
return v___x_16_;
}
case 15:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(15u);
return v___x_17_;
}
case 16:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(16u);
return v___x_18_;
}
case 17:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(17u);
return v___x_19_;
}
case 18:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(18u);
return v___x_20_;
}
case 19:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(19u);
return v___x_21_;
}
case 20:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(20u);
return v___x_22_;
}
default: 
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(21u);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorIdx___boxed(lean_object* v_x_24_){
_start:
{
uint8_t v_x_boxed_25_; lean_object* v_res_26_; 
v_x_boxed_25_ = lean_unbox(v_x_24_);
v_res_26_ = l_Std_Async_Signal_ctorIdx(v_x_boxed_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_toCtorIdx(uint8_t v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Async_Signal_ctorIdx(v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_toCtorIdx___boxed(lean_object* v_x_29_){
_start:
{
uint8_t v_x_4__boxed_30_; lean_object* v_res_31_; 
v_x_4__boxed_30_ = lean_unbox(v_x_29_);
v_res_31_ = l_Std_Async_Signal_toCtorIdx(v_x_4__boxed_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg(lean_object* v_k_32_){
_start:
{
lean_inc(v_k_32_);
return v_k_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___redArg___boxed(lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Async_Signal_ctorElim___redArg(v_k_33_);
lean_dec(v_k_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim(lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, uint8_t v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
lean_inc(v_k_39_);
return v_k_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ctorElim___boxed(lean_object* v_motive_40_, lean_object* v_ctorIdx_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_k_44_){
_start:
{
uint8_t v_t_boxed_45_; lean_object* v_res_46_; 
v_t_boxed_45_ = lean_unbox(v_t_42_);
v_res_46_ = l_Std_Async_Signal_ctorElim(v_motive_40_, v_ctorIdx_41_, v_t_boxed_45_, v_h_43_, v_k_44_);
lean_dec(v_k_44_);
lean_dec(v_ctorIdx_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg(lean_object* v_sighup_47_){
_start:
{
lean_inc(v_sighup_47_);
return v_sighup_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___redArg___boxed(lean_object* v_sighup_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_48_);
lean_dec(v_sighup_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim(lean_object* v_motive_50_, uint8_t v_t_51_, lean_object* v_h_52_, lean_object* v_sighup_53_){
_start:
{
lean_inc(v_sighup_53_);
return v_sighup_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sighup_elim___boxed(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_sighup_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l_Std_Async_Signal_sighup_elim(v_motive_54_, v_t_boxed_58_, v_h_56_, v_sighup_57_);
lean_dec(v_sighup_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg(lean_object* v_sigint_60_){
_start:
{
lean_inc(v_sigint_60_);
return v_sigint_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___redArg___boxed(lean_object* v_sigint_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_61_);
lean_dec(v_sigint_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_sigint_66_){
_start:
{
lean_inc(v_sigint_66_);
return v_sigint_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigint_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_sigint_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l_Std_Async_Signal_sigint_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_sigint_70_);
lean_dec(v_sigint_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg(lean_object* v_sigquit_73_){
_start:
{
lean_inc(v_sigquit_73_);
return v_sigquit_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___redArg___boxed(lean_object* v_sigquit_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_74_);
lean_dec(v_sigquit_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_sigquit_79_){
_start:
{
lean_inc(v_sigquit_79_);
return v_sigquit_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigquit_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_sigquit_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = l_Std_Async_Signal_sigquit_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_sigquit_83_);
lean_dec(v_sigquit_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg(lean_object* v_sigtrap_86_){
_start:
{
lean_inc(v_sigtrap_86_);
return v_sigtrap_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___redArg___boxed(lean_object* v_sigtrap_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_87_);
lean_dec(v_sigtrap_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim(lean_object* v_motive_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_sigtrap_92_){
_start:
{
lean_inc(v_sigtrap_92_);
return v_sigtrap_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtrap_elim___boxed(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_sigtrap_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = l_Std_Async_Signal_sigtrap_elim(v_motive_93_, v_t_boxed_97_, v_h_95_, v_sigtrap_96_);
lean_dec(v_sigtrap_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg(lean_object* v_sigabrt_99_){
_start:
{
lean_inc(v_sigabrt_99_);
return v_sigabrt_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___redArg___boxed(lean_object* v_sigabrt_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_100_);
lean_dec(v_sigabrt_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim(lean_object* v_motive_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_sigabrt_105_){
_start:
{
lean_inc(v_sigabrt_105_);
return v_sigabrt_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigabrt_elim___boxed(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_sigabrt_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = l_Std_Async_Signal_sigabrt_elim(v_motive_106_, v_t_boxed_110_, v_h_108_, v_sigabrt_109_);
lean_dec(v_sigabrt_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg(lean_object* v_sigusr1_112_){
_start:
{
lean_inc(v_sigusr1_112_);
return v_sigusr1_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___redArg___boxed(lean_object* v_sigusr1_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_113_);
lean_dec(v_sigusr1_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim(lean_object* v_motive_115_, uint8_t v_t_116_, lean_object* v_h_117_, lean_object* v_sigusr1_118_){
_start:
{
lean_inc(v_sigusr1_118_);
return v_sigusr1_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr1_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_sigusr1_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = l_Std_Async_Signal_sigusr1_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_sigusr1_122_);
lean_dec(v_sigusr1_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg(lean_object* v_sigusr2_125_){
_start:
{
lean_inc(v_sigusr2_125_);
return v_sigusr2_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___redArg___boxed(lean_object* v_sigusr2_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_126_);
lean_dec(v_sigusr2_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_sigusr2_131_){
_start:
{
lean_inc(v_sigusr2_131_);
return v_sigusr2_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigusr2_elim___boxed(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_sigusr2_135_){
_start:
{
uint8_t v_t_boxed_136_; lean_object* v_res_137_; 
v_t_boxed_136_ = lean_unbox(v_t_133_);
v_res_137_ = l_Std_Async_Signal_sigusr2_elim(v_motive_132_, v_t_boxed_136_, v_h_134_, v_sigusr2_135_);
lean_dec(v_sigusr2_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg(lean_object* v_sigalrm_138_){
_start:
{
lean_inc(v_sigalrm_138_);
return v_sigalrm_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___redArg___boxed(lean_object* v_sigalrm_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_139_);
lean_dec(v_sigalrm_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim(lean_object* v_motive_141_, uint8_t v_t_142_, lean_object* v_h_143_, lean_object* v_sigalrm_144_){
_start:
{
lean_inc(v_sigalrm_144_);
return v_sigalrm_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigalrm_elim___boxed(lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_sigalrm_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = l_Std_Async_Signal_sigalrm_elim(v_motive_145_, v_t_boxed_149_, v_h_147_, v_sigalrm_148_);
lean_dec(v_sigalrm_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg(lean_object* v_sigterm_151_){
_start:
{
lean_inc(v_sigterm_151_);
return v_sigterm_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___redArg___boxed(lean_object* v_sigterm_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_152_);
lean_dec(v_sigterm_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim(lean_object* v_motive_154_, uint8_t v_t_155_, lean_object* v_h_156_, lean_object* v_sigterm_157_){
_start:
{
lean_inc(v_sigterm_157_);
return v_sigterm_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigterm_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_sigterm_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = l_Std_Async_Signal_sigterm_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_sigterm_161_);
lean_dec(v_sigterm_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg(lean_object* v_sigchld_164_){
_start:
{
lean_inc(v_sigchld_164_);
return v_sigchld_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___redArg___boxed(lean_object* v_sigchld_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_165_);
lean_dec(v_sigchld_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_sigchld_170_){
_start:
{
lean_inc(v_sigchld_170_);
return v_sigchld_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigchld_elim___boxed(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_sigchld_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = l_Std_Async_Signal_sigchld_elim(v_motive_171_, v_t_boxed_175_, v_h_173_, v_sigchld_174_);
lean_dec(v_sigchld_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg(lean_object* v_sigcont_177_){
_start:
{
lean_inc(v_sigcont_177_);
return v_sigcont_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___redArg___boxed(lean_object* v_sigcont_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_178_);
lean_dec(v_sigcont_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_sigcont_183_){
_start:
{
lean_inc(v_sigcont_183_);
return v_sigcont_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigcont_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_sigcont_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = l_Std_Async_Signal_sigcont_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_sigcont_187_);
lean_dec(v_sigcont_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg(lean_object* v_sigtstp_190_){
_start:
{
lean_inc(v_sigtstp_190_);
return v_sigtstp_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___redArg___boxed(lean_object* v_sigtstp_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_191_);
lean_dec(v_sigtstp_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_sigtstp_196_){
_start:
{
lean_inc(v_sigtstp_196_);
return v_sigtstp_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigtstp_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_sigtstp_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Std_Async_Signal_sigtstp_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_sigtstp_200_);
lean_dec(v_sigtstp_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg(lean_object* v_sigttin_203_){
_start:
{
lean_inc(v_sigttin_203_);
return v_sigttin_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___redArg___boxed(lean_object* v_sigttin_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_204_);
lean_dec(v_sigttin_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_sigttin_209_){
_start:
{
lean_inc(v_sigttin_209_);
return v_sigttin_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttin_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_sigttin_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Std_Async_Signal_sigttin_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_sigttin_213_);
lean_dec(v_sigttin_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg(lean_object* v_sigttou_216_){
_start:
{
lean_inc(v_sigttou_216_);
return v_sigttou_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___redArg___boxed(lean_object* v_sigttou_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_217_);
lean_dec(v_sigttou_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_sigttou_222_){
_start:
{
lean_inc(v_sigttou_222_);
return v_sigttou_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigttou_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_sigttou_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Std_Async_Signal_sigttou_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_sigttou_226_);
lean_dec(v_sigttou_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg(lean_object* v_sigurg_229_){
_start:
{
lean_inc(v_sigurg_229_);
return v_sigurg_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___redArg___boxed(lean_object* v_sigurg_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_230_);
lean_dec(v_sigurg_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_sigurg_235_){
_start:
{
lean_inc(v_sigurg_235_);
return v_sigurg_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigurg_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_sigurg_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Std_Async_Signal_sigurg_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_sigurg_239_);
lean_dec(v_sigurg_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg(lean_object* v_sigxcpu_242_){
_start:
{
lean_inc(v_sigxcpu_242_);
return v_sigxcpu_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(lean_object* v_sigxcpu_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_243_);
lean_dec(v_sigxcpu_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_sigxcpu_248_){
_start:
{
lean_inc(v_sigxcpu_248_);
return v_sigxcpu_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxcpu_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_sigxcpu_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Std_Async_Signal_sigxcpu_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_sigxcpu_252_);
lean_dec(v_sigxcpu_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg(lean_object* v_sigxfsz_255_){
_start:
{
lean_inc(v_sigxfsz_255_);
return v_sigxfsz_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(lean_object* v_sigxfsz_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_256_);
lean_dec(v_sigxfsz_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_sigxfsz_261_){
_start:
{
lean_inc(v_sigxfsz_261_);
return v_sigxfsz_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigxfsz_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_sigxfsz_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Std_Async_Signal_sigxfsz_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_sigxfsz_265_);
lean_dec(v_sigxfsz_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg(lean_object* v_sigvtalrm_268_){
_start:
{
lean_inc(v_sigvtalrm_268_);
return v_sigvtalrm_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(lean_object* v_sigvtalrm_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_269_);
lean_dec(v_sigvtalrm_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_sigvtalrm_274_){
_start:
{
lean_inc(v_sigvtalrm_274_);
return v_sigvtalrm_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigvtalrm_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_sigvtalrm_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Std_Async_Signal_sigvtalrm_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_sigvtalrm_278_);
lean_dec(v_sigvtalrm_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg(lean_object* v_sigprof_281_){
_start:
{
lean_inc(v_sigprof_281_);
return v_sigprof_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___redArg___boxed(lean_object* v_sigprof_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Async_Signal_sigprof_elim___redArg(v_sigprof_282_);
lean_dec(v_sigprof_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim(lean_object* v_motive_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_sigprof_287_){
_start:
{
lean_inc(v_sigprof_287_);
return v_sigprof_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigprof_elim___boxed(lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_sigprof_291_){
_start:
{
uint8_t v_t_boxed_292_; lean_object* v_res_293_; 
v_t_boxed_292_ = lean_unbox(v_t_289_);
v_res_293_ = l_Std_Async_Signal_sigprof_elim(v_motive_288_, v_t_boxed_292_, v_h_290_, v_sigprof_291_);
lean_dec(v_sigprof_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg(lean_object* v_sigwinch_294_){
_start:
{
lean_inc(v_sigwinch_294_);
return v_sigwinch_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___redArg___boxed(lean_object* v_sigwinch_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_295_);
lean_dec(v_sigwinch_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim(lean_object* v_motive_297_, uint8_t v_t_298_, lean_object* v_h_299_, lean_object* v_sigwinch_300_){
_start:
{
lean_inc(v_sigwinch_300_);
return v_sigwinch_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigwinch_elim___boxed(lean_object* v_motive_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_sigwinch_304_){
_start:
{
uint8_t v_t_boxed_305_; lean_object* v_res_306_; 
v_t_boxed_305_ = lean_unbox(v_t_302_);
v_res_306_ = l_Std_Async_Signal_sigwinch_elim(v_motive_301_, v_t_boxed_305_, v_h_303_, v_sigwinch_304_);
lean_dec(v_sigwinch_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg(lean_object* v_sigio_307_){
_start:
{
lean_inc(v_sigio_307_);
return v_sigio_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___redArg___boxed(lean_object* v_sigio_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_308_);
lean_dec(v_sigio_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim(lean_object* v_motive_310_, uint8_t v_t_311_, lean_object* v_h_312_, lean_object* v_sigio_313_){
_start:
{
lean_inc(v_sigio_313_);
return v_sigio_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigio_elim___boxed(lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_sigio_317_){
_start:
{
uint8_t v_t_boxed_318_; lean_object* v_res_319_; 
v_t_boxed_318_ = lean_unbox(v_t_315_);
v_res_319_ = l_Std_Async_Signal_sigio_elim(v_motive_314_, v_t_boxed_318_, v_h_316_, v_sigio_317_);
lean_dec(v_sigio_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg(lean_object* v_sigsys_320_){
_start:
{
lean_inc(v_sigsys_320_);
return v_sigsys_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___redArg___boxed(lean_object* v_sigsys_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_321_);
lean_dec(v_sigsys_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim(lean_object* v_motive_323_, uint8_t v_t_324_, lean_object* v_h_325_, lean_object* v_sigsys_326_){
_start:
{
lean_inc(v_sigsys_326_);
return v_sigsys_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_sigsys_elim___boxed(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_sigsys_330_){
_start:
{
uint8_t v_t_boxed_331_; lean_object* v_res_332_; 
v_t_boxed_331_ = lean_unbox(v_t_328_);
v_res_332_ = l_Std_Async_Signal_sigsys_elim(v_motive_327_, v_t_boxed_331_, v_h_329_, v_sigsys_330_);
lean_dec(v_sigsys_330_);
return v_res_332_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__44(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(2u);
v___x_400_ = lean_nat_to_int(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Std_Async_instReprSignal_repr___closed__45(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_nat_to_int(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr(uint8_t v_x_403_, lean_object* v_prec_404_){
_start:
{
lean_object* v___y_406_; lean_object* v___y_413_; lean_object* v___y_420_; lean_object* v___y_427_; lean_object* v___y_434_; lean_object* v___y_441_; lean_object* v___y_448_; lean_object* v___y_455_; lean_object* v___y_462_; lean_object* v___y_469_; lean_object* v___y_476_; lean_object* v___y_483_; lean_object* v___y_490_; lean_object* v___y_497_; lean_object* v___y_504_; lean_object* v___y_511_; lean_object* v___y_518_; lean_object* v___y_525_; lean_object* v___y_532_; lean_object* v___y_539_; lean_object* v___y_546_; lean_object* v___y_553_; 
switch(v_x_403_)
{
case 0:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(1024u);
v___x_560_ = lean_nat_dec_le(v___x_559_, v_prec_404_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_406_ = v___x_561_;
goto v___jp_405_;
}
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_406_ = v___x_562_;
goto v___jp_405_;
}
}
case 1:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1024u);
v___x_564_ = lean_nat_dec_le(v___x_563_, v_prec_404_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_413_ = v___x_565_;
goto v___jp_412_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_413_ = v___x_566_;
goto v___jp_412_;
}
}
case 2:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(1024u);
v___x_568_ = lean_nat_dec_le(v___x_567_, v_prec_404_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_420_ = v___x_569_;
goto v___jp_419_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_420_ = v___x_570_;
goto v___jp_419_;
}
}
case 3:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_unsigned_to_nat(1024u);
v___x_572_ = lean_nat_dec_le(v___x_571_, v_prec_404_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_427_ = v___x_573_;
goto v___jp_426_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_427_ = v___x_574_;
goto v___jp_426_;
}
}
case 4:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1024u);
v___x_576_ = lean_nat_dec_le(v___x_575_, v_prec_404_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_434_ = v___x_577_;
goto v___jp_433_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_434_ = v___x_578_;
goto v___jp_433_;
}
}
case 5:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1024u);
v___x_580_ = lean_nat_dec_le(v___x_579_, v_prec_404_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_441_ = v___x_581_;
goto v___jp_440_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_441_ = v___x_582_;
goto v___jp_440_;
}
}
case 6:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1024u);
v___x_584_ = lean_nat_dec_le(v___x_583_, v_prec_404_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_448_ = v___x_585_;
goto v___jp_447_;
}
else
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_448_ = v___x_586_;
goto v___jp_447_;
}
}
case 7:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(1024u);
v___x_588_ = lean_nat_dec_le(v___x_587_, v_prec_404_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_455_ = v___x_589_;
goto v___jp_454_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_455_ = v___x_590_;
goto v___jp_454_;
}
}
case 8:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1024u);
v___x_592_ = lean_nat_dec_le(v___x_591_, v_prec_404_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_462_ = v___x_593_;
goto v___jp_461_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_462_ = v___x_594_;
goto v___jp_461_;
}
}
case 9:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1024u);
v___x_596_ = lean_nat_dec_le(v___x_595_, v_prec_404_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_469_ = v___x_597_;
goto v___jp_468_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_469_ = v___x_598_;
goto v___jp_468_;
}
}
case 10:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1024u);
v___x_600_ = lean_nat_dec_le(v___x_599_, v_prec_404_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_476_ = v___x_601_;
goto v___jp_475_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_476_ = v___x_602_;
goto v___jp_475_;
}
}
case 11:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1024u);
v___x_604_ = lean_nat_dec_le(v___x_603_, v_prec_404_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_483_ = v___x_605_;
goto v___jp_482_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_483_ = v___x_606_;
goto v___jp_482_;
}
}
case 12:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1024u);
v___x_608_ = lean_nat_dec_le(v___x_607_, v_prec_404_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_490_ = v___x_609_;
goto v___jp_489_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_490_ = v___x_610_;
goto v___jp_489_;
}
}
case 13:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_prec_404_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_497_ = v___x_613_;
goto v___jp_496_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_497_ = v___x_614_;
goto v___jp_496_;
}
}
case 14:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1024u);
v___x_616_ = lean_nat_dec_le(v___x_615_, v_prec_404_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_504_ = v___x_617_;
goto v___jp_503_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_504_ = v___x_618_;
goto v___jp_503_;
}
}
case 15:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(1024u);
v___x_620_ = lean_nat_dec_le(v___x_619_, v_prec_404_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_511_ = v___x_621_;
goto v___jp_510_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_511_ = v___x_622_;
goto v___jp_510_;
}
}
case 16:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1024u);
v___x_624_ = lean_nat_dec_le(v___x_623_, v_prec_404_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_518_ = v___x_625_;
goto v___jp_517_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_518_ = v___x_626_;
goto v___jp_517_;
}
}
case 17:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1024u);
v___x_628_ = lean_nat_dec_le(v___x_627_, v_prec_404_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_525_ = v___x_629_;
goto v___jp_524_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_525_ = v___x_630_;
goto v___jp_524_;
}
}
case 18:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1024u);
v___x_632_ = lean_nat_dec_le(v___x_631_, v_prec_404_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_532_ = v___x_633_;
goto v___jp_531_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_532_ = v___x_634_;
goto v___jp_531_;
}
}
case 19:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(1024u);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_prec_404_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_539_ = v___x_637_;
goto v___jp_538_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_539_ = v___x_638_;
goto v___jp_538_;
}
}
case 20:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(1024u);
v___x_640_ = lean_nat_dec_le(v___x_639_, v_prec_404_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_546_ = v___x_641_;
goto v___jp_545_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_546_ = v___x_642_;
goto v___jp_545_;
}
}
default: 
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(1024u);
v___x_644_ = lean_nat_dec_le(v___x_643_, v_prec_404_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__44, &l_Std_Async_instReprSignal_repr___closed__44_once, _init_l_Std_Async_instReprSignal_repr___closed__44);
v___y_553_ = v___x_645_;
goto v___jp_552_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Std_Async_instReprSignal_repr___closed__45, &l_Std_Async_instReprSignal_repr___closed__45_once, _init_l_Std_Async_instReprSignal_repr___closed__45);
v___y_553_ = v___x_646_;
goto v___jp_552_;
}
}
}
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__1));
lean_inc(v___y_406_);
v___x_408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_406_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = 0;
v___x_410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
v___x_411_ = l_Repr_addAppParen(v___x_410_, v_prec_404_);
return v___x_411_;
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__3));
lean_inc(v___y_413_);
v___x_415_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_415_, 0, v___y_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = 0;
v___x_417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v___x_418_ = l_Repr_addAppParen(v___x_417_, v_prec_404_);
return v___x_418_;
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_421_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__5));
lean_inc(v___y_420_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___y_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = 0;
v___x_424_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
v___x_425_ = l_Repr_addAppParen(v___x_424_, v_prec_404_);
return v___x_425_;
}
v___jp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_428_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__7));
lean_inc(v___y_427_);
v___x_429_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_429_, 0, v___y_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = 0;
v___x_431_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*1, v___x_430_);
v___x_432_ = l_Repr_addAppParen(v___x_431_, v_prec_404_);
return v___x_432_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_435_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__9));
lean_inc(v___y_434_);
v___x_436_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_436_, 0, v___y_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = 0;
v___x_438_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*1, v___x_437_);
v___x_439_ = l_Repr_addAppParen(v___x_438_, v_prec_404_);
return v___x_439_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__11));
lean_inc(v___y_441_);
v___x_443_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_443_, 0, v___y_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = 0;
v___x_445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_444_);
v___x_446_ = l_Repr_addAppParen(v___x_445_, v_prec_404_);
return v___x_446_;
}
v___jp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__13));
lean_inc(v___y_448_);
v___x_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = 0;
v___x_452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*1, v___x_451_);
v___x_453_ = l_Repr_addAppParen(v___x_452_, v_prec_404_);
return v___x_453_;
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_456_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__15));
lean_inc(v___y_455_);
v___x_457_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_457_, 0, v___y_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = 0;
v___x_459_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*1, v___x_458_);
v___x_460_ = l_Repr_addAppParen(v___x_459_, v_prec_404_);
return v___x_460_;
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__17));
lean_inc(v___y_462_);
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___y_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
v___x_467_ = l_Repr_addAppParen(v___x_466_, v_prec_404_);
return v___x_467_;
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__19));
lean_inc(v___y_469_);
v___x_471_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_471_, 0, v___y_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = 0;
v___x_473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
v___x_474_ = l_Repr_addAppParen(v___x_473_, v_prec_404_);
return v___x_474_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__21));
lean_inc(v___y_476_);
v___x_478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_478_, 0, v___y_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = 0;
v___x_480_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_479_);
v___x_481_ = l_Repr_addAppParen(v___x_480_, v_prec_404_);
return v___x_481_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__23));
lean_inc(v___y_483_);
v___x_485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_485_, 0, v___y_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = 0;
v___x_487_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*1, v___x_486_);
v___x_488_ = l_Repr_addAppParen(v___x_487_, v_prec_404_);
return v___x_488_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_491_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__25));
lean_inc(v___y_490_);
v___x_492_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_492_, 0, v___y_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = 0;
v___x_494_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*1, v___x_493_);
v___x_495_ = l_Repr_addAppParen(v___x_494_, v_prec_404_);
return v___x_495_;
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_498_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__27));
lean_inc(v___y_497_);
v___x_499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_499_, 0, v___y_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_500_);
v___x_502_ = l_Repr_addAppParen(v___x_501_, v_prec_404_);
return v___x_502_;
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_505_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__29));
lean_inc(v___y_504_);
v___x_506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_506_, 0, v___y_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = 0;
v___x_508_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*1, v___x_507_);
v___x_509_ = l_Repr_addAppParen(v___x_508_, v_prec_404_);
return v___x_509_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__31));
lean_inc(v___y_511_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___y_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
v___x_516_ = l_Repr_addAppParen(v___x_515_, v_prec_404_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_519_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__33));
lean_inc(v___y_518_);
v___x_520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = l_Repr_addAppParen(v___x_522_, v_prec_404_);
return v___x_523_;
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__35));
lean_inc(v___y_525_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___y_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = l_Repr_addAppParen(v___x_529_, v_prec_404_);
return v___x_530_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__37));
lean_inc(v___y_532_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*1, v___x_535_);
v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_404_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_540_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__39));
lean_inc(v___y_539_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___y_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = 0;
v___x_543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_542_);
v___x_544_ = l_Repr_addAppParen(v___x_543_, v_prec_404_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__41));
lean_inc(v___y_546_);
v___x_548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = 0;
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_549_);
v___x_551_ = l_Repr_addAppParen(v___x_550_, v_prec_404_);
return v___x_551_;
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_554_ = ((lean_object*)(l_Std_Async_instReprSignal_repr___closed__43));
lean_inc(v___y_553_);
v___x_555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = 0;
v___x_557_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*1, v___x_556_);
v___x_558_ = l_Repr_addAppParen(v___x_557_, v_prec_404_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_instReprSignal_repr___boxed(lean_object* v_x_647_, lean_object* v_prec_648_){
_start:
{
uint8_t v_x_1241__boxed_649_; lean_object* v_res_650_; 
v_x_1241__boxed_649_ = lean_unbox(v_x_647_);
v_res_650_ = l_Std_Async_instReprSignal_repr(v_x_1241__boxed_649_, v_prec_648_);
lean_dec(v_prec_648_);
return v_res_650_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Signal_ofNat(lean_object* v_n_653_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(10u);
v___x_655_ = lean_nat_dec_le(v_n_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(15u);
v___x_657_ = lean_nat_dec_le(v_n_653_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(18u);
v___x_659_ = lean_nat_dec_le(v_n_653_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(19u);
v___x_661_ = lean_nat_dec_le(v_n_653_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(20u);
v___x_663_ = lean_nat_dec_le(v_n_653_, v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 21;
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 20;
return v___x_665_;
}
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 19;
return v___x_666_;
}
}
else
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(16u);
v___x_668_ = lean_nat_dec_le(v_n_653_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(17u);
v___x_670_ = lean_nat_dec_le(v_n_653_, v___x_669_);
if (v___x_670_ == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 18;
return v___x_671_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = 17;
return v___x_672_;
}
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 16;
return v___x_673_;
}
}
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(12u);
v___x_675_ = lean_nat_dec_le(v_n_653_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(13u);
v___x_677_ = lean_nat_dec_le(v_n_653_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(14u);
v___x_679_ = lean_nat_dec_le(v_n_653_, v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 15;
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 14;
return v___x_681_;
}
}
else
{
uint8_t v___x_682_; 
v___x_682_ = 13;
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(11u);
v___x_684_ = lean_nat_dec_le(v_n_653_, v___x_683_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = 12;
return v___x_685_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = 11;
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(4u);
v___x_688_ = lean_nat_dec_le(v_n_653_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(7u);
v___x_690_ = lean_nat_dec_le(v_n_653_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(8u);
v___x_692_ = lean_nat_dec_le(v_n_653_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(9u);
v___x_694_ = lean_nat_dec_le(v_n_653_, v___x_693_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; 
v___x_695_ = 10;
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 9;
return v___x_696_;
}
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 8;
return v___x_697_;
}
}
else
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(5u);
v___x_699_ = lean_nat_dec_le(v_n_653_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(6u);
v___x_701_ = lean_nat_dec_le(v_n_653_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = 7;
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = 6;
return v___x_703_;
}
}
else
{
uint8_t v___x_704_; 
v___x_704_ = 5;
return v___x_704_;
}
}
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_dec_le(v_n_653_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(2u);
v___x_708_ = lean_nat_dec_le(v_n_653_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(3u);
v___x_710_ = lean_nat_dec_le(v_n_653_, v___x_709_);
if (v___x_710_ == 0)
{
uint8_t v___x_711_; 
v___x_711_ = 4;
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 3;
return v___x_712_;
}
}
else
{
uint8_t v___x_713_; 
v___x_713_ = 2;
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_nat_dec_le(v_n_653_, v___x_714_);
if (v___x_715_ == 0)
{
uint8_t v___x_716_; 
v___x_716_ = 1;
return v___x_716_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_ofNat___boxed(lean_object* v_n_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Std_Async_Signal_ofNat(v_n_718_);
lean_dec(v_n_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instDecidableEqSignal(uint8_t v_x_721_, uint8_t v_y_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = l_Std_Async_Signal_ctorIdx(v_x_721_);
v___x_724_ = l_Std_Async_Signal_ctorIdx(v_y_722_);
v___x_725_ = lean_nat_dec_eq(v___x_723_, v___x_724_);
lean_dec(v___x_724_);
lean_dec(v___x_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instDecidableEqSignal___boxed(lean_object* v_x_726_, lean_object* v_y_727_){
_start:
{
uint8_t v_x_13__boxed_728_; uint8_t v_y_14__boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_x_13__boxed_728_ = lean_unbox(v_x_726_);
v_y_14__boxed_729_ = lean_unbox(v_y_727_);
v_res_730_ = l_Std_Async_instDecidableEqSignal(v_x_13__boxed_728_, v_y_14__boxed_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_instBEqSignal_beq(uint8_t v_x_732_, uint8_t v_y_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = l_Std_Async_Signal_ctorIdx(v_x_732_);
v___x_735_ = l_Std_Async_Signal_ctorIdx(v_y_733_);
v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
lean_dec(v___x_735_);
lean_dec(v___x_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_instBEqSignal_beq___boxed(lean_object* v_x_737_, lean_object* v_y_738_){
_start:
{
uint8_t v_x_17__boxed_739_; uint8_t v_y_18__boxed_740_; uint8_t v_res_741_; lean_object* v_r_742_; 
v_x_17__boxed_739_ = lean_unbox(v_x_737_);
v_y_18__boxed_740_ = lean_unbox(v_y_738_);
v_res_741_ = l_Std_Async_instBEqSignal_beq(v_x_17__boxed_739_, v_y_18__boxed_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0(void){
_start:
{
lean_object* v___x_745_; uint32_t v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_int32_of_nat(v___x_745_);
return v___x_746_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1(void){
_start:
{
lean_object* v___x_747_; uint32_t v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(2u);
v___x_748_ = lean_int32_of_nat(v___x_747_);
return v___x_748_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2(void){
_start:
{
lean_object* v___x_749_; uint32_t v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(3u);
v___x_750_ = lean_int32_of_nat(v___x_749_);
return v___x_750_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3(void){
_start:
{
lean_object* v___x_751_; uint32_t v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(5u);
v___x_752_ = lean_int32_of_nat(v___x_751_);
return v___x_752_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4(void){
_start:
{
lean_object* v___x_753_; uint32_t v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(6u);
v___x_754_ = lean_int32_of_nat(v___x_753_);
return v___x_754_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5(void){
_start:
{
lean_object* v___x_755_; uint32_t v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(10u);
v___x_756_ = lean_int32_of_nat(v___x_755_);
return v___x_756_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6(void){
_start:
{
lean_object* v___x_757_; uint32_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(12u);
v___x_758_ = lean_int32_of_nat(v___x_757_);
return v___x_758_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7(void){
_start:
{
lean_object* v___x_759_; uint32_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(14u);
v___x_760_ = lean_int32_of_nat(v___x_759_);
return v___x_760_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8(void){
_start:
{
lean_object* v___x_761_; uint32_t v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(15u);
v___x_762_ = lean_int32_of_nat(v___x_761_);
return v___x_762_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9(void){
_start:
{
lean_object* v___x_763_; uint32_t v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(17u);
v___x_764_ = lean_int32_of_nat(v___x_763_);
return v___x_764_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10(void){
_start:
{
lean_object* v___x_765_; uint32_t v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(18u);
v___x_766_ = lean_int32_of_nat(v___x_765_);
return v___x_766_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11(void){
_start:
{
lean_object* v___x_767_; uint32_t v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(20u);
v___x_768_ = lean_int32_of_nat(v___x_767_);
return v___x_768_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12(void){
_start:
{
lean_object* v___x_769_; uint32_t v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(21u);
v___x_770_ = lean_int32_of_nat(v___x_769_);
return v___x_770_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13(void){
_start:
{
lean_object* v___x_771_; uint32_t v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(22u);
v___x_772_ = lean_int32_of_nat(v___x_771_);
return v___x_772_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14(void){
_start:
{
lean_object* v___x_773_; uint32_t v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(23u);
v___x_774_ = lean_int32_of_nat(v___x_773_);
return v___x_774_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15(void){
_start:
{
lean_object* v___x_775_; uint32_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(24u);
v___x_776_ = lean_int32_of_nat(v___x_775_);
return v___x_776_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16(void){
_start:
{
lean_object* v___x_777_; uint32_t v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(25u);
v___x_778_ = lean_int32_of_nat(v___x_777_);
return v___x_778_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17(void){
_start:
{
lean_object* v___x_779_; uint32_t v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(26u);
v___x_780_ = lean_int32_of_nat(v___x_779_);
return v___x_780_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18(void){
_start:
{
lean_object* v___x_781_; uint32_t v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(27u);
v___x_782_ = lean_int32_of_nat(v___x_781_);
return v___x_782_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19(void){
_start:
{
lean_object* v___x_783_; uint32_t v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(28u);
v___x_784_ = lean_int32_of_nat(v___x_783_);
return v___x_784_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20(void){
_start:
{
lean_object* v___x_785_; uint32_t v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(29u);
v___x_786_ = lean_int32_of_nat(v___x_785_);
return v___x_786_;
}
}
static uint32_t _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21(void){
_start:
{
lean_object* v___x_787_; uint32_t v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(31u);
v___x_788_ = lean_int32_of_nat(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT uint32_t l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(uint8_t v_x_789_){
_start:
{
switch(v_x_789_)
{
case 0:
{
uint32_t v___x_790_; 
v___x_790_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0);
return v___x_790_;
}
case 1:
{
uint32_t v___x_791_; 
v___x_791_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1);
return v___x_791_;
}
case 2:
{
uint32_t v___x_792_; 
v___x_792_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2);
return v___x_792_;
}
case 3:
{
uint32_t v___x_793_; 
v___x_793_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3);
return v___x_793_;
}
case 4:
{
uint32_t v___x_794_; 
v___x_794_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4);
return v___x_794_;
}
case 5:
{
uint32_t v___x_795_; 
v___x_795_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5);
return v___x_795_;
}
case 6:
{
uint32_t v___x_796_; 
v___x_796_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6);
return v___x_796_;
}
case 7:
{
uint32_t v___x_797_; 
v___x_797_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7);
return v___x_797_;
}
case 8:
{
uint32_t v___x_798_; 
v___x_798_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8);
return v___x_798_;
}
case 9:
{
uint32_t v___x_799_; 
v___x_799_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9);
return v___x_799_;
}
case 10:
{
uint32_t v___x_800_; 
v___x_800_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10);
return v___x_800_;
}
case 11:
{
uint32_t v___x_801_; 
v___x_801_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11);
return v___x_801_;
}
case 12:
{
uint32_t v___x_802_; 
v___x_802_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12);
return v___x_802_;
}
case 13:
{
uint32_t v___x_803_; 
v___x_803_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13);
return v___x_803_;
}
case 14:
{
uint32_t v___x_804_; 
v___x_804_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14);
return v___x_804_;
}
case 15:
{
uint32_t v___x_805_; 
v___x_805_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15);
return v___x_805_;
}
case 16:
{
uint32_t v___x_806_; 
v___x_806_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16);
return v___x_806_;
}
case 17:
{
uint32_t v___x_807_; 
v___x_807_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17);
return v___x_807_;
}
case 18:
{
uint32_t v___x_808_; 
v___x_808_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18);
return v___x_808_;
}
case 19:
{
uint32_t v___x_809_; 
v___x_809_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19);
return v___x_809_;
}
case 20:
{
uint32_t v___x_810_; 
v___x_810_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20);
return v___x_810_;
}
default: 
{
uint32_t v___x_811_; 
v___x_811_ = lean_uint32_once(&l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21, &l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once, _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(lean_object* v_x_812_){
_start:
{
uint8_t v_x_356__boxed_813_; uint32_t v_res_814_; lean_object* v_r_815_; 
v_x_356__boxed_813_ = lean_unbox(v_x_812_);
v_res_814_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_813_);
v_r_815_ = lean_box_uint32(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk(uint8_t v_signum_816_, uint8_t v_repeating_817_){
_start:
{
uint32_t v___x_819_; lean_object* v___x_820_; 
v___x_819_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_816_);
v___x_820_ = lean_uv_signal_mk(v___x_819_, v_repeating_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_820_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_820_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_mk___boxed(lean_object* v_signum_837_, lean_object* v_repeating_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_signum_boxed_840_; uint8_t v_repeating_boxed_841_; lean_object* v_res_842_; 
v_signum_boxed_840_ = lean_unbox(v_signum_837_);
v_repeating_boxed_841_ = lean_unbox(v_repeating_838_);
v_res_842_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_840_, v_repeating_boxed_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___lam__0(lean_object* v___x_843_, lean_object* v_x_844_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_mk_io_user_error(v___x_843_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___x_843_);
v_val_847_ = lean_ctor_get(v_x_844_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v_x_844_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v_x_844_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_val_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait(lean_object* v_s_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_uv_signal_next(v_s_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_873_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_873_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_873_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___f_865_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_866_ = lean_io_promise_result_opt(v_a_861_);
lean_dec(v_a_861_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = 1;
v___x_869_ = lean_task_map(v___f_865_, v___x_866_, v___x_867_, v___x_868_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_869_);
v___x_871_ = v___x_863_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_860_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_860_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_wait___boxed(lean_object* v_s_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Async_Signal_Waiter_wait(v_s_882_);
lean_dec(v_s_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop(lean_object* v_s_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_uv_signal_stop(v_s_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_stop___boxed(lean_object* v_s_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_Async_Signal_Waiter_stop(v_s_888_);
lean_dec(v_s_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(lean_object* v_w_893_, lean_object* v_lose_894_){
_start:
{
lean_object* v_finished_896_; lean_object* v_promise_897_; lean_object* v___x_898_; uint8_t v___y_900_; uint8_t v___x_908_; 
v_finished_896_ = lean_ctor_get(v_w_893_, 0);
v_promise_897_ = lean_ctor_get(v_w_893_, 1);
v___x_898_ = lean_st_ref_take(v_finished_896_);
v___x_908_ = lean_unbox(v___x_898_);
lean_dec(v___x_898_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; 
v___x_909_ = 1;
v___y_900_ = v___x_909_;
goto v___jp_899_;
}
else
{
uint8_t v___x_910_; 
v___x_910_ = 0;
v___y_900_ = v___x_910_;
goto v___jp_899_;
}
v___jp_899_:
{
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = 1;
v___x_902_ = lean_box(v___x_901_);
v___x_903_ = lean_st_ref_set(v_finished_896_, v___x_902_);
if (v___y_900_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_apply_1(v_lose_894_, lean_box(0));
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v_lose_894_);
v___x_905_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0));
v___x_906_ = lean_io_promise_resolve(v___x_905_, v_promise_897_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(lean_object* v_w_911_, lean_object* v_lose_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_w_911_, v_lose_912_);
lean_dec_ref(v_w_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0(lean_object* v_s_915_){
_start:
{
lean_object* v_val_918_; lean_object* v___x_920_; 
v___x_920_ = lean_uv_signal_cancel(v_s_915_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 1);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_val_918_ = v___x_926_;
goto v___jp_917_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_920_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_920_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 0);
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
v_val_918_ = v___x_934_;
goto v___jp_917_;
}
}
}
v___jp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_val_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__0___boxed(lean_object* v_s_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_s_937_);
lean_dec(v_s_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1(lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_a_946_ = lean_ctor_get(v_x_944_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_944_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v_x_944_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v_x_944_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec_ref(v_x_944_);
v___x_955_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__1___closed__1));
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__1___boxed(lean_object* v_x_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_Async_Signal_Waiter_selector___lam__1(v_x_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2(lean_object* v___f_965_, lean_object* v_s_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v___f_965_);
v_a_969_ = lean_ctor_get(v_x_967_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v_x_967_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v_x_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_999_; 
v_a_978_ = lean_ctor_get(v_x_967_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_999_ == 0)
{
v___x_980_ = v_x_967_;
v_isShared_981_ = v_isSharedCheck_999_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v_x_967_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_999_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_val_983_; uint8_t v___x_988_; 
v___x_988_ = lean_unbox(v_a_978_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_uv_signal_cancel(v_s_966_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_a_990_);
v___x_992_ = v___x_980_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_val_983_ = v___x_992_;
goto v___jp_982_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___x_989_);
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
lean_ctor_set(v___x_980_, 0, v_a_994_);
v___x_996_ = v___x_980_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
v_val_983_ = v___x_996_;
goto v___jp_982_;
}
}
}
else
{
lean_object* v___x_998_; 
lean_del_object(v___x_980_);
lean_dec(v_a_978_);
lean_dec_ref(v___f_965_);
v___x_998_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__2___closed__2));
return v___x_998_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_val_983_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_unbox(v_a_978_);
lean_dec(v_a_978_);
v___x_987_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_985_, v___x_986_, v___x_984_, v___f_965_);
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__2___boxed(lean_object* v___f_1000_, lean_object* v_s_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Async_Signal_Waiter_selector___lam__2(v___f_1000_, v_s_1001_, v_x_1002_);
lean_dec(v_s_1001_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__3(lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v_x_1005_);
v___x_1007_ = lean_task_pure(v_a_1006_);
return v___x_1007_;
}
else
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_a_1008_);
lean_dec_ref(v_x_1005_);
return v_a_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5(lean_object* v_s_1009_){
_start:
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v___x_1014_ = lean_uv_signal_next(v_s_1009_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1027_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1027_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1027_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___f_1019_ = ((lean_object*)(l_Std_Async_Signal_Waiter_wait___closed__1));
v___x_1020_ = lean_io_promise_result_opt(v_a_1015_);
lean_dec(v_a_1015_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = 1;
v___x_1023_ = lean_task_map(v___f_1019_, v___x_1020_, v___x_1021_, v___x_1022_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1023_);
v___x_1025_ = v___x_1017_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
v_val_1012_ = v___x_1025_;
goto v___jp_1011_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1014_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1014_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v_val_1012_ = v___x_1033_;
goto v___jp_1011_;
}
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_val_1012_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__5___boxed(lean_object* v_s_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_1036_);
lean_dec(v_s_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4(lean_object* v___f_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_apply_1(v___f_1039_, lean_box(0));
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__4___boxed(lean_object* v___f_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_Async_Signal_Waiter_selector___lam__4(v___f_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6(lean_object* v___x_1045_, lean_object* v___f_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___f_1046_);
lean_dec(v___x_1045_);
v_a_1049_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1051_ = v_x_1047_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v_x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1074_; 
v_a_1058_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1060_ = v_x_1047_;
v_isShared_1061_ = v_isSharedCheck_1074_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v_x_1047_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1074_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
uint8_t v___x_1062_; uint8_t v_val_1064_; 
v___x_1062_ = lean_io_get_task_state(v_a_1058_);
lean_dec(v_a_1058_);
if (v___x_1062_ == 2)
{
uint8_t v___x_1072_; 
v___x_1072_ = 1;
v_val_1064_ = v___x_1072_;
goto v___jp_1063_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = 0;
v_val_1064_ = v___x_1073_;
goto v___jp_1063_;
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(v_val_1064_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1065_);
v___x_1067_ = v___x_1060_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___x_1069_ = 0;
v___x_1070_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1045_, v___x_1069_, v___x_1068_, v___f_1046_);
return v___x_1070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__6___boxed(lean_object* v___x_1075_, lean_object* v___f_1076_, lean_object* v_x_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_Async_Signal_Waiter_selector___lam__6(v___x_1075_, v___f_1076_, v_x_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7(lean_object* v___f_1080_, lean_object* v___x_1081_, lean_object* v___f_1082_, lean_object* v___f_1083_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
lean_inc_n(v___x_1081_, 2);
v___x_1085_ = lean_io_as_task(v___f_1080_, v___x_1081_);
v___x_1086_ = 1;
v___x_1087_ = lean_task_bind(v___x_1085_, v___f_1082_, v___x_1081_, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
v___x_1090_ = 0;
v___x_1091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1090_, v___x_1089_, v___f_1083_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__7___boxed(lean_object* v___f_1092_, lean_object* v___x_1093_, lean_object* v___f_1094_, lean_object* v___f_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Async_Signal_Waiter_selector___lam__7(v___f_1092_, v___x_1093_, v___f_1094_, v___f_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8(lean_object* v___x_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__8___boxed(lean_object* v___x_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___x_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9(lean_object* v_waiter_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_a_1110_; 
if (lean_obj_tag(v_a_1107_) == 0)
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v_a_1107_);
v_a_1110_ = v_a_1112_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
v_isSharedCheck_1123_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_a_1107_, 0);
lean_dec(v_unused_1124_);
v___x_1114_ = v_a_1107_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v_a_1107_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___f_1116_; lean_object* v___x_1117_; 
v___f_1116_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__9___closed__0));
v___x_1117_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(v_waiter_1106_, v___f_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_a_1118_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v_a_1122_; 
lean_del_object(v___x_1114_);
v_a_1122_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1117_);
v_a_1110_ = v_a_1122_;
goto v___jp_1109_;
}
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_a_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__9___boxed(lean_object* v_waiter_1125_, lean_object* v_a_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_Async_Signal_Waiter_selector___lam__9(v_waiter_1125_, v_a_1126_);
lean_dec_ref(v_waiter_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10(lean_object* v___f_1131_, lean_object* v___x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v___x_1132_);
lean_dec_ref(v___f_1131_);
v_a_1135_ = lean_ctor_get(v_x_1133_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v_x_1133_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v_x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v_x_1133_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v_x_1133_);
v___x_1145_ = 0;
v___x_1146_ = lean_io_map_task(v___f_1131_, v_a_1144_, v___x_1132_, v___x_1145_);
lean_dec_ref(v___x_1146_);
v___x_1147_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___lam__10___closed__0));
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__10___boxed(lean_object* v___f_1148_, lean_object* v___x_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Async_Signal_Waiter_selector___lam__10(v___f_1148_, v___x_1149_, v_x_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11(lean_object* v___f_1153_, lean_object* v___x_1154_, lean_object* v_waiter_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___f_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1157_ = lean_apply_1(v___f_1153_, lean_box(0));
v___f_1158_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1158_, 0, v_waiter_1155_);
lean_inc(v___x_1154_);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__10___boxed), 4, 2);
lean_closure_set(v___f_1159_, 0, v___f_1158_);
lean_closure_set(v___f_1159_, 1, v___x_1154_);
v___x_1160_ = 0;
v___x_1161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1154_, v___x_1160_, v___x_1157_, v___f_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector___lam__11___boxed(lean_object* v___f_1162_, lean_object* v___x_1163_, lean_object* v_waiter_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_Async_Signal_Waiter_selector___lam__11(v___f_1162_, v___x_1163_, v_waiter_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Signal_Waiter_selector(lean_object* v_s_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
lean_inc_n(v_s_1169_, 2);
v___f_1170_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1170_, 0, v_s_1169_);
v___f_1171_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__0));
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1172_, 0, v___f_1171_);
lean_closure_set(v___f_1172_, 1, v_s_1169_);
v___f_1173_ = ((lean_object*)(l_Std_Async_Signal_Waiter_selector___closed__1));
v___f_1174_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_1174_, 0, v_s_1169_);
lean_inc_ref(v___f_1174_);
v___f_1175_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1175_, 0, v___f_1174_);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___f_1177_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1177_, 0, v___x_1176_);
lean_closure_set(v___f_1177_, 1, v___f_1172_);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__7___boxed), 5, 4);
lean_closure_set(v___f_1178_, 0, v___f_1175_);
lean_closure_set(v___f_1178_, 1, v___x_1176_);
lean_closure_set(v___f_1178_, 2, v___f_1173_);
lean_closure_set(v___f_1178_, 3, v___f_1177_);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_Async_Signal_Waiter_selector___lam__11___boxed), 4, 2);
lean_closure_set(v___f_1179_, 0, v___f_1174_);
lean_closure_set(v___f_1179_, 1, v___x_1176_);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v___f_1178_);
lean_ctor_set(v___x_1180_, 1, v___f_1179_);
lean_ctor_set(v___x_1180_, 2, v___f_1170_);
return v___x_1180_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Signal(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Signal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
