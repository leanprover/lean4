// Lean compiler output
// Module: Std.Async.Process
// Imports: public import Std.Time public import Std.Internal.UV.System public import Std.Data.HashMap import Init.Data.Ord.UInt
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
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uv_chdir(lean_object*);
lean_object* lean_uv_set_process_title(lean_object*);
lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_uv_get_free_memory();
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Std_Internal_UV_System_getrusage___boxed(lean_object*);
lean_object* l_Functor_mapRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_get_process_title();
lean_object* lean_uv_os_getpid();
lean_object* lean_uv_cwd();
lean_object* lean_uv_get_total_memory();
lean_object* lean_uv_os_getpriority(uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_uv_exepath();
lean_object* lean_uv_os_getppid();
lean_object* lean_uv_get_available_memory();
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_Std_Time_Millisecond_instInhabitedOffset;
lean_object* lean_uv_get_constrained_memory();
lean_object* lean_uv_os_setpriority(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_IO_Process_instReprResourceUsageStats_repr_spec__0(lean_object*);
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cpuUserTime"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3_value),((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cpuSystemTime"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "peakResidentSetSizeKb"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "sharedMemorySizeKb"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unsharedDataSizeKb"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unsharedStackSizeKb"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "minorPageFaults"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "majorPageFaults"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "swapOperations"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "blockInputOps"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "blockOutputOps"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "messagesSent"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "messagesReceived"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "signalsReceived"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43_value;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "voluntaryContextSwitches"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "involuntaryContextSwitches"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49;
static const lean_string_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51;
static lean_once_cell_t l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53_value;
static const lean_ctor_object l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50_value)}};
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54_value;
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_IO_Process_instReprResourceUsageStats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IO_Process_instReprResourceUsageStats_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IO_Process_instReprResourceUsageStats___closed__0 = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_IO_Process_instReprResourceUsageStats = (const lean_object*)&l_Std_IO_Process_instReprResourceUsageStats___closed__0_value;
static lean_once_cell_t l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0;
static lean_once_cell_t l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1;
LEAN_EXPORT lean_object* l_Std_IO_Process_instInhabitedResourceUsageStats_default;
LEAN_EXPORT lean_object* l_Std_IO_Process_instInhabitedResourceUsageStats;
LEAN_EXPORT uint64_t l_Std_IO_Process_instInhabitedPId_default;
LEAN_EXPORT uint64_t l_Std_IO_Process_instInhabitedPId;
LEAN_EXPORT uint8_t l_Std_IO_Process_instDecidableEqPId_decEq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_IO_Process_instDecidableEqPId_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_IO_Process_instDecidableEqPId(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_IO_Process_instDecidableEqPId___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_IO_Process_instOrdPId_ord(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_IO_Process_instOrdPId_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_IO_Process_instOrdPId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IO_Process_instOrdPId_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IO_Process_instOrdPId___closed__0 = (const lean_object*)&l_Std_IO_Process_instOrdPId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_IO_Process_instOrdPId = (const lean_object*)&l_Std_IO_Process_instOrdPId___closed__0_value;
static const lean_string_object l_Std_IO_Process_instReprPId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "PId.mk "};
static const lean_object* l_Std_IO_Process_instReprPId___lam__0___closed__0 = (const lean_object*)&l_Std_IO_Process_instReprPId___lam__0___closed__0_value;
static const lean_ctor_object l_Std_IO_Process_instReprPId___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_IO_Process_instReprPId___lam__0___closed__0_value)}};
static const lean_object* l_Std_IO_Process_instReprPId___lam__0___closed__1 = (const lean_object*)&l_Std_IO_Process_instReprPId___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprPId___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprPId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_IO_Process_instReprPId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IO_Process_instReprPId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IO_Process_instReprPId___closed__0 = (const lean_object*)&l_Std_IO_Process_instReprPId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_IO_Process_instReprPId = (const lean_object*)&l_Std_IO_Process_instReprPId___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IO_Process_getProcessTitle();
LEAN_EXPORT lean_object* l_Std_IO_Process_getProcessTitle___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_setProcessTitle(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_setProcessTitle___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getId();
LEAN_EXPORT lean_object* l_Std_IO_Process_getId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getParentId();
LEAN_EXPORT lean_object* l_Std_IO_Process_getParentId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getCwd();
LEAN_EXPORT lean_object* l_Std_IO_Process_getCwd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_setCwd(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_setCwd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getPriority(uint64_t);
LEAN_EXPORT lean_object* l_Std_IO_Process_getPriority___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_setPriority(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_IO_Process_setPriority___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_IO_Process_getResourceUsage___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_IO_Process_getResourceUsage___closed__0;
static const lean_closure_object l_Std_IO_Process_getResourceUsage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IO_Process_getResourceUsage___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IO_Process_getResourceUsage___closed__1 = (const lean_object*)&l_Std_IO_Process_getResourceUsage___closed__1_value;
static const lean_closure_object l_Std_IO_Process_getResourceUsage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_UV_System_getrusage___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IO_Process_getResourceUsage___closed__2 = (const lean_object*)&l_Std_IO_Process_getResourceUsage___closed__2_value;
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage();
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_getExecutablePath();
LEAN_EXPORT lean_object* l_Std_IO_Process_getExecutablePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_freeMemory();
LEAN_EXPORT lean_object* l_Std_IO_Process_freeMemory___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_totalMemory();
LEAN_EXPORT lean_object* l_Std_IO_Process_totalMemory___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_constrainedMemory();
LEAN_EXPORT lean_object* l_Std_IO_Process_constrainedMemory___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IO_Process_availableMemory();
LEAN_EXPORT lean_object* l_Std_IO_Process_availableMemory___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_IO_Process_instReprResourceUsageStats_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(15u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(17u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(25u);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(22u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(23u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(19u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(18u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(16u);
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(20u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(28u);
v___x_80_ = lean_nat_to_int(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(30u);
v___x_85_ = lean_nat_to_int(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0));
v___x_88_ = lean_string_length(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51);
v___x_90_ = lean_nat_to_int(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(lean_object* v_x_95_){
_start:
{
lean_object* v_cpuUserTime_96_; lean_object* v_cpuSystemTime_97_; uint64_t v_peakResidentSetSizeKb_98_; uint64_t v_sharedMemorySizeKb_99_; uint64_t v_unsharedDataSizeKb_100_; uint64_t v_unsharedStackSizeKb_101_; uint64_t v_minorPageFaults_102_; uint64_t v_majorPageFaults_103_; uint64_t v_swapOperations_104_; uint64_t v_blockInputOps_105_; uint64_t v_blockOutputOps_106_; uint64_t v_messagesSent_107_; uint64_t v_messagesReceived_108_; uint64_t v_signalsReceived_109_; uint64_t v_voluntaryContextSwitches_110_; uint64_t v_involuntaryContextSwitches_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_cpuUserTime_96_ = lean_ctor_get(v_x_95_, 0);
v_cpuSystemTime_97_ = lean_ctor_get(v_x_95_, 1);
v_peakResidentSetSizeKb_98_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2);
v_sharedMemorySizeKb_99_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 8);
v_unsharedDataSizeKb_100_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 16);
v_unsharedStackSizeKb_101_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 24);
v_minorPageFaults_102_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 32);
v_majorPageFaults_103_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 40);
v_swapOperations_104_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 48);
v_blockInputOps_105_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 56);
v_blockOutputOps_106_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 64);
v_messagesSent_107_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 72);
v_messagesReceived_108_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 80);
v_signalsReceived_109_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 88);
v_voluntaryContextSwitches_110_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 96);
v_involuntaryContextSwitches_111_ = lean_ctor_get_uint64(v_x_95_, sizeof(void*)*2 + 104);
v___x_112_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5));
v___x_113_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6));
v___x_114_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_cpuUserTime_96_, v___x_115_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_114_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_113_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9));
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_box(1);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11));
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_112_);
v___x_128_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12);
v___x_129_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_cpuSystemTime_97_, v___x_115_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_118_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_127_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_121_);
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_123_);
v___x_135_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_112_);
v___x_138_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15);
v___x_139_ = lean_uint64_to_nat(v_peakResidentSetSizeKb_98_);
v___x_140_ = l_Nat_reprFast(v___x_139_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
v___x_142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_138_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_118_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_137_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_121_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_123_);
v___x_147_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17));
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_112_);
v___x_150_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18);
v___x_151_ = lean_uint64_to_nat(v_sharedMemorySizeKb_99_);
v___x_152_ = l_Nat_reprFast(v___x_151_);
v___x_153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_150_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_118_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_149_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_121_);
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_123_);
v___x_159_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20));
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_112_);
v___x_162_ = lean_uint64_to_nat(v_unsharedDataSizeKb_100_);
v___x_163_ = l_Nat_reprFast(v___x_162_);
v___x_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_150_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_118_);
v___x_167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_161_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_121_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_123_);
v___x_170_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22));
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_112_);
v___x_173_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23);
v___x_174_ = lean_uint64_to_nat(v_unsharedStackSizeKb_101_);
v___x_175_ = l_Nat_reprFast(v___x_174_);
v___x_176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_173_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_118_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_172_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_121_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_123_);
v___x_182_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25));
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_112_);
v___x_185_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26);
v___x_186_ = lean_uint64_to_nat(v_minorPageFaults_102_);
v___x_187_ = l_Nat_reprFast(v___x_186_);
v___x_188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___x_189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_185_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_118_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_184_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_121_);
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_123_);
v___x_194_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28));
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_112_);
v___x_197_ = lean_uint64_to_nat(v_majorPageFaults_103_);
v___x_198_ = l_Nat_reprFast(v___x_197_);
v___x_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
v___x_200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_185_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_118_);
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_196_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_121_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_123_);
v___x_205_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30));
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_112_);
v___x_208_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31);
v___x_209_ = lean_uint64_to_nat(v_swapOperations_104_);
v___x_210_ = l_Nat_reprFast(v___x_209_);
v___x_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_208_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_118_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_207_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_121_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_123_);
v___x_217_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33));
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_112_);
v___x_220_ = lean_uint64_to_nat(v_blockInputOps_105_);
v___x_221_ = l_Nat_reprFast(v___x_220_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_128_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_118_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_219_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_121_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_123_);
v___x_228_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_112_);
v___x_231_ = lean_uint64_to_nat(v_blockOutputOps_106_);
v___x_232_ = l_Nat_reprFast(v___x_231_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_208_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_118_);
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_230_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_121_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_123_);
v___x_239_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_112_);
v___x_242_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38);
v___x_243_ = lean_uint64_to_nat(v_messagesSent_107_);
v___x_244_ = l_Nat_reprFast(v___x_243_);
v___x_245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
v___x_246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_242_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_118_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_241_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_121_);
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_123_);
v___x_251_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40));
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_112_);
v___x_254_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41);
v___x_255_ = lean_uint64_to_nat(v_messagesReceived_108_);
v___x_256_ = l_Nat_reprFast(v___x_255_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_118_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_253_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_121_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_123_);
v___x_263_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43));
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_112_);
v___x_266_ = lean_uint64_to_nat(v_signalsReceived_109_);
v___x_267_ = l_Nat_reprFast(v___x_266_);
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_185_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_118_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_265_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_121_);
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_123_);
v___x_274_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45));
v___x_275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_112_);
v___x_277_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46);
v___x_278_ = lean_uint64_to_nat(v_voluntaryContextSwitches_110_);
v___x_279_ = l_Nat_reprFast(v___x_278_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_277_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_118_);
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_276_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_121_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_123_);
v___x_286_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48));
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_112_);
v___x_289_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49);
v___x_290_ = lean_uint64_to_nat(v_involuntaryContextSwitches_111_);
v___x_291_ = l_Nat_reprFast(v___x_290_);
v___x_292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_289_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_118_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_288_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52, &l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52_once, _init_l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52);
v___x_297_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53));
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_295_);
v___x_299_ = ((lean_object*)(l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54));
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_296_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_118_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___redArg___boxed(lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(v_x_303_);
lean_dec_ref(v_x_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr(lean_object* v_x_305_, lean_object* v_prec_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_IO_Process_instReprResourceUsageStats_repr___redArg(v_x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprResourceUsageStats_repr___boxed(lean_object* v_x_308_, lean_object* v_prec_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_IO_Process_instReprResourceUsageStats_repr(v_x_308_, v_prec_309_);
lean_dec(v_prec_309_);
lean_dec_ref(v_x_308_);
return v_res_310_;
}
}
static uint64_t _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0(void){
_start:
{
lean_object* v___x_313_; uint64_t v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_uint64_of_nat(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1(void){
_start:
{
uint64_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_uint64_once(&l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0, &l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once, _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0);
v___x_316_ = l_Std_Time_Millisecond_instInhabitedOffset;
v___x_317_ = lean_alloc_ctor(0, 2, 112);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 8, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 16, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 24, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 32, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 40, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 48, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 56, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 64, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 72, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 80, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 88, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 96, v___x_315_);
lean_ctor_set_uint64(v___x_317_, sizeof(void*)*2 + 104, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1, &l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1_once, _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__1);
return v___x_318_;
}
}
static lean_object* _init_l_Std_IO_Process_instInhabitedResourceUsageStats(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_IO_Process_instInhabitedResourceUsageStats_default;
return v___x_319_;
}
}
static uint64_t _init_l_Std_IO_Process_instInhabitedPId_default(void){
_start:
{
uint64_t v___x_320_; 
v___x_320_ = lean_uint64_once(&l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0, &l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0_once, _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default___closed__0);
return v___x_320_;
}
}
static uint64_t _init_l_Std_IO_Process_instInhabitedPId(void){
_start:
{
uint64_t v___x_321_; 
v___x_321_ = l_Std_IO_Process_instInhabitedPId_default;
return v___x_321_;
}
}
LEAN_EXPORT uint8_t l_Std_IO_Process_instDecidableEqPId_decEq(uint64_t v_x_322_, uint64_t v_x_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_uint64_dec_eq(v_x_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instDecidableEqPId_decEq___boxed(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint64_t v_x_25__boxed_327_; uint64_t v_x_26__boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_x_25__boxed_327_ = lean_unbox_uint64(v_x_325_);
lean_dec_ref(v_x_325_);
v_x_26__boxed_328_ = lean_unbox_uint64(v_x_326_);
lean_dec_ref(v_x_326_);
v_res_329_ = l_Std_IO_Process_instDecidableEqPId_decEq(v_x_25__boxed_327_, v_x_26__boxed_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_Std_IO_Process_instDecidableEqPId(uint64_t v_x_331_, uint64_t v_x_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_uint64_dec_eq(v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instDecidableEqPId___boxed(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint64_t v_x_6__boxed_336_; uint64_t v_x_7__boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_x_6__boxed_336_ = lean_unbox_uint64(v_x_334_);
lean_dec_ref(v_x_334_);
v_x_7__boxed_337_ = lean_unbox_uint64(v_x_335_);
lean_dec_ref(v_x_335_);
v_res_338_ = l_Std_IO_Process_instDecidableEqPId(v_x_6__boxed_336_, v_x_7__boxed_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Std_IO_Process_instOrdPId_ord(uint64_t v_x_340_, uint64_t v_x_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_uint64_dec_lt(v_x_340_, v_x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_uint64_dec_eq(v_x_340_, v_x_341_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 2;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instOrdPId_ord___boxed(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint64_t v_x_75__boxed_349_; uint64_t v_x_76__boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_x_75__boxed_349_ = lean_unbox_uint64(v_x_347_);
lean_dec_ref(v_x_347_);
v_x_76__boxed_350_ = lean_unbox_uint64(v_x_348_);
lean_dec_ref(v_x_348_);
v_res_351_ = l_Std_IO_Process_instOrdPId_ord(v_x_75__boxed_349_, v_x_76__boxed_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprPId___lam__0(uint64_t v_u_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_360_ = ((lean_object*)(l_Std_IO_Process_instReprPId___lam__0___closed__1));
v___x_361_ = lean_uint64_to_nat(v_u_358_);
v___x_362_ = l_Nat_reprFast(v___x_361_);
v___x_363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_360_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Repr_addAppParen(v___x_364_, v___y_359_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_instReprPId___lam__0___boxed(lean_object* v_u_366_, lean_object* v___y_367_){
_start:
{
uint64_t v_u_boxed_368_; lean_object* v_res_369_; 
v_u_boxed_368_ = lean_unbox_uint64(v_u_366_);
lean_dec_ref(v_u_366_);
v_res_369_ = l_Std_IO_Process_instReprPId___lam__0(v_u_boxed_368_, v___y_367_);
lean_dec(v___y_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getProcessTitle(){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_uv_get_process_title();
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getProcessTitle___boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_IO_Process_getProcessTitle();
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setProcessTitle(lean_object* v_title_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_uv_set_process_title(v_title_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setProcessTitle___boxed(lean_object* v_title_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_IO_Process_setProcessTitle(v_title_379_);
lean_dec_ref(v_title_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getId(){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_383_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_383_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getId___boxed(lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_IO_Process_getId();
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getParentId(){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_uv_os_getppid();
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_403_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_403_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getParentId___boxed(lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_IO_Process_getParentId();
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getCwd(){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_uv_cwd();
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_423_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_423_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getCwd___boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_IO_Process_getCwd();
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setCwd(lean_object* v_path_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_uv_chdir(v_path_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setCwd___boxed(lean_object* v_path_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_IO_Process_setCwd(v_path_445_);
lean_dec_ref(v_path_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getPriority(uint64_t v_pid_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = lean_uv_os_getpriority(v_pid_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getPriority___boxed(lean_object* v_pid_451_, lean_object* v_a_452_){
_start:
{
uint64_t v_pid_boxed_453_; lean_object* v_res_454_; 
v_pid_boxed_453_ = lean_unbox_uint64(v_pid_451_);
lean_dec_ref(v_pid_451_);
v_res_454_ = l_Std_IO_Process_getPriority(v_pid_boxed_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setPriority(uint64_t v_pid_455_, uint64_t v_priority_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_uv_os_setpriority(v_pid_455_, v_priority_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_setPriority___boxed(lean_object* v_pid_459_, lean_object* v_priority_460_, lean_object* v_a_461_){
_start:
{
uint64_t v_pid_boxed_462_; uint64_t v_priority_boxed_463_; lean_object* v_res_464_; 
v_pid_boxed_462_ = lean_unbox_uint64(v_pid_459_);
lean_dec_ref(v_pid_459_);
v_priority_boxed_463_ = lean_unbox_uint64(v_priority_460_);
lean_dec_ref(v_priority_460_);
v_res_464_ = l_Std_IO_Process_setPriority(v_pid_boxed_462_, v_priority_boxed_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___lam__0(lean_object* v_rusage_465_){
_start:
{
uint64_t v_userTime_466_; uint64_t v_systemTime_467_; uint64_t v_maxRSS_468_; uint64_t v_ixRSS_469_; uint64_t v_idRSS_470_; uint64_t v_isRSS_471_; uint64_t v_minFlt_472_; uint64_t v_majFlt_473_; uint64_t v_nSwap_474_; uint64_t v_inBlock_475_; uint64_t v_outBlock_476_; uint64_t v_msgSent_477_; uint64_t v_msgRecv_478_; uint64_t v_signals_479_; uint64_t v_voluntaryCS_480_; uint64_t v_involuntaryCS_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_userTime_466_ = lean_ctor_get_uint64(v_rusage_465_, 0);
v_systemTime_467_ = lean_ctor_get_uint64(v_rusage_465_, 8);
v_maxRSS_468_ = lean_ctor_get_uint64(v_rusage_465_, 16);
v_ixRSS_469_ = lean_ctor_get_uint64(v_rusage_465_, 24);
v_idRSS_470_ = lean_ctor_get_uint64(v_rusage_465_, 32);
v_isRSS_471_ = lean_ctor_get_uint64(v_rusage_465_, 40);
v_minFlt_472_ = lean_ctor_get_uint64(v_rusage_465_, 48);
v_majFlt_473_ = lean_ctor_get_uint64(v_rusage_465_, 56);
v_nSwap_474_ = lean_ctor_get_uint64(v_rusage_465_, 64);
v_inBlock_475_ = lean_ctor_get_uint64(v_rusage_465_, 72);
v_outBlock_476_ = lean_ctor_get_uint64(v_rusage_465_, 80);
v_msgSent_477_ = lean_ctor_get_uint64(v_rusage_465_, 88);
v_msgRecv_478_ = lean_ctor_get_uint64(v_rusage_465_, 96);
v_signals_479_ = lean_ctor_get_uint64(v_rusage_465_, 104);
v_voluntaryCS_480_ = lean_ctor_get_uint64(v_rusage_465_, 112);
v_involuntaryCS_481_ = lean_ctor_get_uint64(v_rusage_465_, 120);
v___x_482_ = lean_uint64_to_nat(v_userTime_466_);
v___x_483_ = lean_nat_to_int(v___x_482_);
v___x_484_ = lean_uint64_to_nat(v_systemTime_467_);
v___x_485_ = lean_nat_to_int(v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 2, 112);
lean_ctor_set(v___x_486_, 0, v___x_483_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2, v_maxRSS_468_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 8, v_ixRSS_469_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 16, v_idRSS_470_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 24, v_isRSS_471_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 32, v_minFlt_472_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 40, v_majFlt_473_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 48, v_nSwap_474_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 56, v_inBlock_475_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 64, v_outBlock_476_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 72, v_msgSent_477_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 80, v_msgRecv_478_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 88, v_signals_479_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 96, v_voluntaryCS_480_);
lean_ctor_set_uint64(v___x_486_, sizeof(void*)*2 + 104, v_involuntaryCS_481_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___lam__0___boxed(lean_object* v_rusage_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_IO_Process_getResourceUsage___lam__0(v_rusage_487_);
lean_dec_ref(v_rusage_487_);
return v_res_488_;
}
}
static lean_object* _init_l_Std_IO_Process_getResourceUsage___closed__0(void){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_instMonadEIO(lean_box(0));
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage(){
_start:
{
lean_object* v___x_493_; lean_object* v_toApplicative_494_; lean_object* v_toFunctor_495_; lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v___x_28__overap_498_; lean_object* v___x_499_; 
v___x_493_ = lean_obj_once(&l_Std_IO_Process_getResourceUsage___closed__0, &l_Std_IO_Process_getResourceUsage___closed__0_once, _init_l_Std_IO_Process_getResourceUsage___closed__0);
v_toApplicative_494_ = lean_ctor_get(v___x_493_, 0);
v_toFunctor_495_ = lean_ctor_get(v_toApplicative_494_, 0);
v___f_496_ = ((lean_object*)(l_Std_IO_Process_getResourceUsage___closed__1));
v___x_497_ = ((lean_object*)(l_Std_IO_Process_getResourceUsage___closed__2));
lean_inc_ref(v_toFunctor_495_);
v___x_28__overap_498_ = l_Functor_mapRev___redArg(v_toFunctor_495_, v___x_497_, v___f_496_);
v___x_499_ = lean_apply_1(v___x_28__overap_498_, lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getResourceUsage___boxed(lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_IO_Process_getResourceUsage();
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getExecutablePath(){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_uv_exepath();
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_503_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_getExecutablePath___boxed(lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_IO_Process_getExecutablePath();
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_freeMemory(){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_uv_get_free_memory();
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_freeMemory___boxed(lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_IO_Process_freeMemory();
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_totalMemory(){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_uv_get_total_memory();
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_totalMemory___boxed(lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_IO_Process_totalMemory();
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_constrainedMemory(){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_uv_get_constrained_memory();
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_constrainedMemory___boxed(lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_IO_Process_constrainedMemory();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_availableMemory(){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_uv_get_available_memory();
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_IO_Process_availableMemory___boxed(lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_IO_Process_availableMemory();
return v_res_537_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_System(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Process(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_IO_Process_instInhabitedResourceUsageStats_default = _init_l_Std_IO_Process_instInhabitedResourceUsageStats_default();
lean_mark_persistent(l_Std_IO_Process_instInhabitedResourceUsageStats_default);
l_Std_IO_Process_instInhabitedResourceUsageStats = _init_l_Std_IO_Process_instInhabitedResourceUsageStats();
lean_mark_persistent(l_Std_IO_Process_instInhabitedResourceUsageStats);
l_Std_IO_Process_instInhabitedPId_default = _init_l_Std_IO_Process_instInhabitedPId_default();
l_Std_IO_Process_instInhabitedPId = _init_l_Std_IO_Process_instInhabitedPId();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Process(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_System(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Process(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Process(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Process(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Process(builtin);
}
#ifdef __cplusplus
}
#endif
