// Lean compiler output
// Module: Lake.Build.Common
// Imports: public import Lake.Build.Job.Monad public import Lake.Config.Monad public import Lake.Util.JsonObject public import Lake.Util.IO public import Lake.Build.Actions
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
lean_object* l_instMonadST(lean_object*);
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__0;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__1 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__2 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__3 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__4 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__5 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__6 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__7 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__8 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__9 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__10 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__0, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__11 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__12 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__13 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__13_value;
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__14 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__14_value;
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__17 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value;
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EStateT_instPure___redArg___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__18 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__18_value;
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
extern lean_object* l_System_Platform_target;
uint64_t lean_string_hash(lean_object*);
static lean_once_cell_t l_Lake_platformTrace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__0;
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_once_cell_t l_Lake_platformTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_platformTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_platformTrace___closed__2 = (const lean_object*)&l_Lake_platformTrace___closed__2_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lake_platformTrace___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__3;
static lean_once_cell_t l_Lake_platformTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__4;
static lean_once_cell_t l_Lake_platformTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Lake_platformTrace;
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_addPureTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_addPureTrace___redArg___closed__0 = (const lean_object*)&l_Lake_addPureTrace___redArg___closed__0_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-09-10"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__0_value;
static const lean_ctor_object l_Lake_BuildMetadata_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__1_value;
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_BuildMetadata_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_toJson___closed__2;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depHash"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__3_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "log"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__6_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "synthetic"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__7_value;
lean_object* l_Lake_Hash_hex(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object*);
static const lean_closure_object l_Lake_instToJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonBuildMetadata = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_ofStub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_ofStub___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_ofStub___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value;
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "synthetic: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "log: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "outputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: depHash"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "depHash: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid trace: expected string 'depHash' of decimal digits"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value;
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid trace stub: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown trace format: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid trace: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "unknown trace format: expected JSON number or object"};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__4_value;
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object*);
static const lean_closure_object l_Lake_instFromJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_fromJson_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonBuildMetadata = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_readTraceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": read failed: "};
static const lean_object* l_Lake_readTraceFile___closed__0 = (const lean_object*)&l_Lake_readTraceFile___closed__0_value;
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonPUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonPUnit___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonPUnit = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
static const lean_string_object l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instToOutputJsonArtifact___lam__0___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonArtifact___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonArtifact___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonArtifact = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "target is out-of-date and needs to be rebuilt"};
static const lean_object* l_Lake_buildAction___redArg___closed__0 = (const lean_object*)&l_Lake_buildAction___redArg___closed__0_value;
static const lean_ctor_object l_Lake_buildAction___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_buildAction___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_buildAction___redArg___closed__1 = (const lean_object*)&l_Lake_buildAction___redArg___closed__1_value;
static const lean_string_object l_Lake_buildAction___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nobuild"};
static const lean_object* l_Lake_buildAction___redArg___closed__2 = (const lean_object*)&l_Lake_buildAction___redArg___closed__2_value;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_writeFileHash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".hash"};
static const lean_object* l_Lake_writeFileHash___closed__0 = (const lean_object*)&l_Lake_writeFileHash___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileUnlessUpToDate_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".trace"};
static const lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0 = (const lean_object*)&l_Lake_buildFileUnlessUpToDate_x27___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1(lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_saveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to cache artifact: "};
static const lean_object* l_Lake_Cache_saveArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_saveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_saveArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__1_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__2 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value;
static lean_once_cell_t l_Lake_Cache_saveArtifact___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Cache_saveArtifact___closed__3;
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_cacheArtifact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_cacheArtifact___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_cacheArtifact___redArg___closed__0 = (const lean_object*)&l_Lake_cacheArtifact___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n- "};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not write outputs to cache: "};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lake_getArtifacts_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getArtifacts_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__2_value;
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__3_value;
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "downloaded succeeded, but artifact failed to resolve: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__0_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "downloaded artifact "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__1 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__1_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__2 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__2_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__3 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__3_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "could not mark downloaded artifact read-only: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__4 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__4_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "artifact with associated cache service but no scope"};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__5 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__5_value;
static const lean_ctor_object l_Lake_resolveArtifact___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_resolveArtifact___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__6 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__6_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "artifact cache service is not configured: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__7 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__7_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "artifact not found in cache:\n  "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__8 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__8_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__9 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__9_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1_value;
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_restoreArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "restored artifact from cache to: "};
static const lean_object* l_Lake_restoreArtifact___closed__0 = (const lean_object*)&l_Lake_restoreArtifact___closed__0_value;
static const lean_string_object l_Lake_restoreArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "found artifact in cache: "};
static const lean_object* l_Lake_restoreArtifact___closed__1 = (const lean_object*)&l_Lake_restoreArtifact___closed__1_value;
static const lean_string_object l_Lake_restoreArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "could not hard link artifact, copying from cache instead; error: "};
static const lean_object* l_Lake_restoreArtifact___closed__2 = (const lean_object*)&l_Lake_restoreArtifact___closed__2_value;
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "failed to retrieve artifact modification time: "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_inputBinFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_inputBinFile___redArg___closed__0 = (const lean_object*)&l_Lake_inputBinFile___redArg___closed__0_value;
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_inputDir___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_inputDir___lam__1___closed__0 = (const lean_object*)&l_Lake_inputDir___lam__1___closed__0_value;
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_inputDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_inputDir___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_inputDir___closed__0 = (const lean_object*)&l_Lake_inputDir___closed__0_value;
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildO___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "traceArgs: "};
static const lean_object* l_Lake_buildO___lam__2___closed__0 = (const lean_object*)&l_Lake_buildO___lam__2___closed__0_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lake_buildO___lam__2___closed__1 = (const lean_object*)&l_Lake_buildO___lam__2___closed__1_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_buildO___lam__2___closed__2 = (const lean_object*)&l_Lake_buildO___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_buildO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_buildO___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__0 = (const lean_object*)&l_Lake_buildO___closed__0_value;
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_buildO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__1 = (const lean_object*)&l_Lake_buildO___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildLeanO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lake_buildLeanO___lam__0___closed__0 = (const lean_object*)&l_Lake_buildLeanO___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_buildLeanO___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lake_buildStaticLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "objs"};
static const lean_object* l_Lake_buildStaticLib___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-l"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value;
static const lean_array_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSharedLib___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__3___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
extern lean_object* l_Lake_instDataKindDynlib;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
static lean_once_cell_t l_Lake_buildLeanSharedLib___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
x_2 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__14));
x_3 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__0, &l_Lake_instMonadWorkspaceJobM___closed__0_once, _init_l_Lake_instMonadWorkspaceJobM___closed__0);
x_2 = l_Lake_instAlternativeELogTOfMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
x_2 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__15, &l_Lake_instMonadWorkspaceJobM___closed__15_once, _init_l_Lake_instMonadWorkspaceJobM___closed__15);
x_3 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__19, &l_Lake_instMonadWorkspaceJobM___closed__19_once, _init_l_Lake_instMonadWorkspaceJobM___closed__19);
x_2 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__18));
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 3);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_80; 
x_1 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__0, &l_Lake_instMonadWorkspaceJobM___closed__0_once, _init_l_Lake_instMonadWorkspaceJobM___closed__0);
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_80 = !lean_is_exclusive(x_1);
if (x_80 == 0)
{
x_4 = x_1;
x_5 = x_80;
goto block_79;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_75; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_75 = !lean_is_exclusive(x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_2, 4);
lean_dec(x_76);
x_77 = lean_ctor_get(x_2, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_dec(x_78);
x_8 = x_2;
x_9 = x_75;
goto block_74;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_3);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_3);
lean_inc(x_3);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_3);
lean_inc_ref(x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_15, 0, x_7);
lean_inc_ref(x_14);
if (x_9 == 0)
{
lean_ctor_set(x_8, 4, x_11);
lean_ctor_set(x_8, 3, x_12);
lean_ctor_set(x_8, 2, x_13);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_14);
x_16 = x_8;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_14);
lean_ctor_set(x_73, 1, x_15);
lean_ctor_set(x_73, 2, x_13);
lean_ctor_set(x_73, 3, x_12);
lean_ctor_set(x_73, 4, x_11);
x_16 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_17; 
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_16);
x_17 = x_4;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_16);
lean_ctor_set(x_71, 1, x_10);
x_17 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_68; 
lean_inc_ref(x_14);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_14);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__16, &l_Lake_instMonadWorkspaceJobM___closed__16_once, _init_l_Lake_instMonadWorkspaceJobM___closed__16);
lean_inc_ref(x_17);
x_22 = l_ReaderT_instAlternativeOfMonad___redArg(x_21, x_17);
x_23 = l_ReaderT_instMonad___redArg(x_17);
lean_inc_ref(x_23);
x_24 = l_ReaderT_instAlternativeOfMonad___redArg(x_22, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_25);
x_27 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__20, &l_Lake_instMonadWorkspaceJobM___closed__20_once, _init_l_Lake_instMonadWorkspaceJobM___closed__20);
lean_inc_ref(x_20);
x_28 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_27, x_20);
x_29 = l_ReaderT_instMonad___redArg(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_30);
x_32 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_28, x_20);
x_33 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, lean_box(0));
lean_closure_set(x_33, 2, lean_box(0));
lean_closure_set(x_33, 3, lean_box(0));
lean_closure_set(x_33, 4, x_32);
lean_inc_ref(x_26);
x_34 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_33, x_26);
lean_inc_ref(x_31);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_31);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_ReaderT_instMonad___redArg(x_29);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_40);
lean_dec_ref(x_39);
x_41 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_34, x_26);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_42, 0, lean_box(0));
lean_closure_set(x_42, 1, x_41);
lean_inc_ref(x_37);
x_43 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_42, x_37);
x_44 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_43, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_45, 0, lean_box(0));
lean_closure_set(x_45, 1, x_44);
lean_inc_ref(x_40);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_40);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_inc_ref(x_48);
x_49 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_45, x_48);
lean_inc_ref(x_48);
x_50 = l_Lake_EquipT_instFunctor___redArg(x_48);
x_51 = lean_ctor_get(x_38, 0);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_38, 1);
lean_dec(x_69);
x_52 = x_38;
x_53 = x_68;
goto block_67;
}
else
{
lean_inc(x_51);
lean_dec(x_38);
x_52 = lean_box(0);
x_53 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_51);
x_55 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_49, x_48);
x_56 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, lean_box(0));
lean_closure_set(x_56, 2, lean_box(0));
lean_closure_set(x_56, 3, x_55);
lean_inc_ref(x_50);
x_57 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_56, x_50);
x_58 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_57, x_50);
x_59 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_59, 0, lean_box(0));
lean_closure_set(x_59, 1, x_58);
lean_inc_ref(x_54);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_54);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_54);
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_60);
x_62 = x_52;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_61);
x_62 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lake_EquipT_instFunctor___redArg(x_62);
x_64 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_59, x_63);
return x_64;
}
}
}
}
}
}
}
}
static uint64_t _init_l_Lake_platformTrace___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_System_Platform_target;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1(void) {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = lean_uint64_once(&l_Lake_platformTrace___closed__0, &l_Lake_platformTrace___closed__0_once, _init_l_Lake_platformTrace___closed__0);
x_2 = l_Lake_Hash_nil;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4(void) {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_obj_once(&l_Lake_platformTrace___closed__3, &l_Lake_platformTrace___closed__3_once, _init_l_Lake_platformTrace___closed__3);
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5(void) {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_2 = lean_uint64_once(&l_Lake_platformTrace___closed__1, &l_Lake_platformTrace___closed__1_once, _init_l_Lake_platformTrace___closed__1);
x_3 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_4 = l_System_Platform_target;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_platformTrace(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_platformTrace___closed__5, &l_Lake_platformTrace___closed__5_once, _init_l_Lake_platformTrace___closed__5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_8 = x_1;
x_9 = x_18;
goto block_17;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lake_platformTrace;
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_6, x_10);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_12);
x_13 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_5);
x_13 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_addPlatformTrace___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 2);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_13 = x_6;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lake_platformTrace;
x_16 = lean_box(0);
x_17 = l_Lake_BuildTrace_mix(x_11, x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_17);
x_18 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_10);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addPlatformTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_19; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_9 = x_2;
x_10 = x_19;
goto block_18;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = l_Lake_BuildTrace_mix(x_7, x_11);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_13);
x_14 = x_9;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_6);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_addLeanTrace___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 2);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_13 = x_6;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_5);
x_16 = lean_box(0);
x_17 = l_Lake_BuildTrace_mix(x_11, x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_17);
x_18 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_10);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addLeanTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
x_12 = x_5;
x_13 = x_30;
goto block_29;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_3);
x_14 = lean_apply_1(x_2, x_3);
x_15 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_16 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_17 = lean_string_append(x_4, x_16);
x_18 = lean_apply_1(x_1, x_3);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_21 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_unbox_uint64(x_14);
lean_dec_ref(x_14);
lean_ctor_set_uint64(x_21, sizeof(void*)*3, x_22);
x_23 = lean_box(0);
x_24 = l_Lake_BuildTrace_mix(x_10, x_21);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_24);
x_25 = x_12;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_11);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_9);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_addPureTrace___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_36; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
x_18 = x_11;
x_19 = x_36;
goto block_35;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_13);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_4);
x_20 = lean_apply_1(x_3, x_4);
x_21 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_22 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_23 = lean_string_append(x_5, x_22);
x_24 = lean_apply_1(x_2, x_4);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_27 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_unbox_uint64(x_20);
lean_dec_ref(x_20);
lean_ctor_set_uint64(x_27, sizeof(void*)*3, x_28);
x_29 = lean_box(0);
x_30 = l_Lake_BuildTrace_mix(x_16, x_27);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_30);
x_31 = x_18;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_17);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_14);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_15);
x_31 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_addPureTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_array_push(x_7, x_3);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_instToJsonLogEntry_toJson(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__1));
x_2 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
x_3 = lean_box(1);
x_4 = l_Lake_JsonObject_insertJson(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_7 = lean_obj_once(&l_Lake_BuildMetadata_toJson___closed__2, &l_Lake_BuildMetadata_toJson___closed__2_once, _init_l_Lake_BuildMetadata_toJson___closed__2);
x_8 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
x_9 = l_Lake_Hash_hex(x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_JsonObject_insertJson(x_7, x_8, x_10);
x_12 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
x_13 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(x_3);
x_14 = l_Lake_JsonObject_insertJson(x_11, x_12, x_13);
x_15 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
x_16 = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(x_4);
lean_dec(x_4);
x_17 = l_Lake_JsonObject_insertJson(x_14, x_15, x_16);
x_18 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
x_19 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(x_5);
x_20 = l_Lake_JsonObject_insertJson(x_17, x_18, x_19);
x_21 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
x_22 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_22, 0, x_6);
x_23 = l_Lake_JsonObject_insertJson(x_20, x_21, x_22);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 8, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_Lake_BuildMetadata_ofStub(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getBool_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
x_5 = x_3;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Lake_instFromJsonLogEntry_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
x_2 = x_1;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget_borrowed(x_11, x_15);
lean_inc(x_16);
x_17 = l_Lean_Json_getStr_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_11);
x_18 = lean_ctor_get(x_17, 0);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
x_19 = x_17;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_26 = lean_ctor_get(x_17, 0);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
x_27 = x_17;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_array_fget(x_11, x_29);
lean_dec_ref(x_11);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_31);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
x_2 = x_1;
goto block_10;
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = ((lean_object*)(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint8_t x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_79; uint64_t x_80; uint64_t x_83; lean_object* x_84; uint64_t x_110; uint64_t x_113; lean_object* x_139; lean_object* x_140; 
x_139 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
x_140 = l_Lake_JsonObject_getJson_x3f(x_1, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
x_142 = l_Lake_JsonObject_getJson_x3f(x_1, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = l_Lean_Json_getStr_x3f(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_155; 
x_146 = lean_ctor_get(x_145, 0);
x_155 = !lean_is_exclusive(x_145);
if (x_155 == 0)
{
x_147 = x_145;
x_148 = x_155;
goto block_154;
}
else
{
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_box(0);
x_148 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_150 = lean_string_append(x_149, x_146);
lean_dec(x_146);
if (x_148 == 0)
{
lean_ctor_set(x_147, 0, x_150);
x_151 = x_147;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
else
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
x_156 = lean_ctor_get(x_145, 0);
x_163 = !lean_is_exclusive(x_145);
if (x_163 == 0)
{
x_157 = x_145;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_145);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
lean_ctor_set_tag(x_157, 0);
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_145, 0);
lean_inc(x_164);
lean_dec_ref(x_145);
x_165 = l_Lake_Hash_ofDecimal_x3f(x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return x_166;
}
else
{
lean_object* x_167; uint64_t x_168; 
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_unbox_uint64(x_167);
lean_dec(x_167);
x_113 = x_168;
goto block_138;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_140);
x_169 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
x_170 = l_Lake_JsonObject_getJson_x3f(x_1, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = l_Lake_Hash_fromJson_x3f(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_183; 
x_174 = lean_ctor_get(x_173, 0);
x_183 = !lean_is_exclusive(x_173);
if (x_183 == 0)
{
x_175 = x_173;
x_176 = x_183;
goto block_182;
}
else
{
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_178 = lean_string_append(x_177, x_174);
lean_dec(x_174);
if (x_176 == 0)
{
lean_ctor_set(x_175, 0, x_178);
x_179 = x_175;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_178);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
}
else
{
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_191; 
x_184 = lean_ctor_get(x_173, 0);
x_191 = !lean_is_exclusive(x_173);
if (x_191 == 0)
{
x_185 = x_173;
x_186 = x_191;
goto block_190;
}
else
{
lean_inc(x_184);
lean_dec(x_173);
x_185 = lean_box(0);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_186 == 0)
{
lean_ctor_set_tag(x_185, 0);
x_187 = x_185;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_184);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
else
{
lean_object* x_192; uint64_t x_193; 
x_192 = lean_ctor_get(x_173, 0);
lean_inc(x_192);
lean_dec_ref(x_173);
x_193 = lean_unbox_uint64(x_192);
lean_dec(x_192);
x_113 = x_193;
goto block_138;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set_uint64(x_7, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 8, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_15:
{
uint8_t x_14; 
x_14 = 0;
x_2 = x_10;
x_3 = x_12;
x_4 = x_11;
x_5 = x_13;
x_6 = x_14;
goto block_9;
}
block_45:
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
x_21 = l_Lake_JsonObject_getJson_x3f(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_33; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
x_24 = lean_ctor_get(x_23, 0);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
x_25 = x_23;
x_26 = x_33;
goto block_32;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
x_28 = lean_string_append(x_27, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
x_34 = lean_ctor_get(x_23, 0);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
x_35 = x_23;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set_tag(x_35, 0);
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec_ref(x_23);
if (lean_obj_tag(x_42) == 0)
{
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_2 = x_16;
x_3 = x_19;
x_4 = x_17;
x_5 = x_18;
x_6 = x_44;
goto block_9;
}
}
}
}
}
block_50:
{
lean_object* x_49; 
x_49 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
x_16 = x_46;
x_17 = x_47;
x_18 = x_48;
x_19 = x_49;
goto block_45;
}
block_78:
{
lean_object* x_54; lean_object* x_55; 
x_54 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
x_55 = l_Lake_JsonObject_getJson_x3f(x_1, x_54);
if (lean_obj_tag(x_55) == 0)
{
x_46 = x_51;
x_47 = x_53;
x_48 = x_52;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_67; 
lean_dec(x_53);
lean_dec_ref(x_51);
x_58 = lean_ctor_get(x_57, 0);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
x_59 = x_57;
x_60 = x_67;
goto block_66;
}
else
{
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
x_62 = lean_string_append(x_61, x_58);
lean_dec(x_58);
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_62);
x_63 = x_59;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
else
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_53);
lean_dec_ref(x_51);
x_68 = lean_ctor_get(x_57, 0);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
x_69 = x_57;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
lean_ctor_set_tag(x_69, 0);
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
lean_dec_ref(x_57);
if (lean_obj_tag(x_76) == 0)
{
x_46 = x_51;
x_47 = x_53;
x_48 = x_52;
goto block_50;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_16 = x_51;
x_17 = x_53;
x_18 = x_52;
x_19 = x_77;
goto block_45;
}
}
}
}
}
block_82:
{
lean_object* x_81; 
x_81 = lean_box(0);
x_51 = x_79;
x_52 = x_80;
x_53 = x_81;
goto block_78;
}
block_109:
{
lean_object* x_85; lean_object* x_86; 
x_85 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
x_86 = l_Lake_JsonObject_getJson_x3f(x_1, x_85);
if (lean_obj_tag(x_86) == 0)
{
x_79 = x_84;
x_80 = x_83;
goto block_82;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_98; 
lean_dec_ref(x_84);
x_89 = lean_ctor_get(x_88, 0);
x_98 = !lean_is_exclusive(x_88);
if (x_98 == 0)
{
x_90 = x_88;
x_91 = x_98;
goto block_97;
}
else
{
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_box(0);
x_91 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
x_93 = lean_string_append(x_92, x_89);
lean_dec(x_89);
if (x_91 == 0)
{
lean_ctor_set(x_90, 0, x_93);
x_94 = x_90;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_93);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
else
{
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec_ref(x_84);
x_99 = lean_ctor_get(x_88, 0);
x_106 = !lean_is_exclusive(x_88);
if (x_106 == 0)
{
x_100 = x_88;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_88);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
lean_ctor_set_tag(x_100, 0);
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_88, 0);
lean_inc(x_107);
lean_dec_ref(x_88);
if (lean_obj_tag(x_107) == 0)
{
x_79 = x_84;
x_80 = x_83;
goto block_82;
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_51 = x_84;
x_52 = x_83;
x_53 = x_108;
goto block_78;
}
}
}
}
}
block_112:
{
lean_object* x_111; 
x_111 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
x_83 = x_110;
x_84 = x_111;
goto block_109;
}
block_138:
{
lean_object* x_114; lean_object* x_115; 
x_114 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
x_115 = l_Lake_JsonObject_getJson_x3f(x_1, x_114);
if (lean_obj_tag(x_115) == 0)
{
x_110 = x_113;
goto block_112;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
x_117 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_127; 
x_118 = lean_ctor_get(x_117, 0);
x_127 = !lean_is_exclusive(x_117);
if (x_127 == 0)
{
x_119 = x_117;
x_120 = x_127;
goto block_126;
}
else
{
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_box(0);
x_120 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
x_122 = lean_string_append(x_121, x_118);
lean_dec(x_118);
if (x_120 == 0)
{
lean_ctor_set(x_119, 0, x_122);
x_123 = x_119;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_122);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
else
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
x_128 = lean_ctor_get(x_117, 0);
x_135 = !lean_is_exclusive(x_117);
if (x_135 == 0)
{
x_129 = x_117;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_117);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
lean_ctor_set_tag(x_129, 0);
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec_ref(x_117);
if (lean_obj_tag(x_136) == 0)
{
x_110 = x_113;
goto block_112;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_83 = x_113;
x_84 = x_137;
goto block_109;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_fromJsonObject_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lake_Hash_ofJsonNumber_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_15 = x_3;
x_16 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unbox_uint64(x_14);
lean_dec(x_14);
x_18 = l_Lake_BuildMetadata_ofStub(x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
case 5:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_Lake_BuildMetadata_fromJsonObject_x3f(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_51; 
x_26 = lean_ctor_get(x_25, 0);
x_51 = !lean_is_exclusive(x_25);
if (x_51 == 0)
{
x_27 = x_25;
x_28 = x_51;
goto block_50;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_35; lean_object* x_36; 
x_35 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
x_36 = l_Lake_JsonObject_getJson_x3f(x_24, x_35);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 3)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_49; 
x_38 = lean_ctor_get(x_37, 0);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
x_39 = x_37;
x_40 = x_49;
goto block_48;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_41; uint8_t x_42; 
x_41 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
x_42 = lean_string_dec_eq(x_38, x_41);
lean_dec_ref(x_38);
if (x_42 == 0)
{
lean_del_object(x_39);
goto block_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_del_object(x_27);
x_43 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
x_44 = lean_string_append(x_43, x_26);
lean_dec(x_26);
if (x_40 == 0)
{
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_44);
x_45 = x_39;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_dec(x_37);
goto block_34;
}
}
else
{
lean_dec(x_36);
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
x_30 = lean_string_append(x_29, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
return x_25;
}
}
default: 
{
lean_object* x_52; 
x_52 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_fromJson_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = l_Lake_BuildMetadata_fromJson_x3f(x_11);
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = 1;
x_6 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set_uint64(x_6, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 8, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Lake_BuildMetadata_ofFetch(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_17 = lean_array_get_size(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
x_21 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(x_20);
x_7 = x_21;
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lake_Hash_hex(x_16);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_7 = x_23;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_push(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_3;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_7, x_8, x_3);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_10, x_11, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_6 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set_uint64(x_9, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 8, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildMetadata_ofBuild___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_2, x_4);
x_7 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_BuildMetadata_ofBuild(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_SavedTrace_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_SavedTrace_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_SavedTrace_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_16; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_16 = l_Lean_Json_parse(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_6 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lake_BuildMetadata_fromJson_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_6 = x_20;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_19, 0);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
x_22 = x_19;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 2);
x_24 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_24 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
}
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_string_append(x_8, x_6);
lean_dec_ref(x_6);
x_10 = 2;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_2, x_11);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec_ref(x_4);
if (lean_obj_tag(x_30) == 11)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = ((lean_object*)(l_Lake_readTraceFile___closed__0));
x_34 = lean_string_append(x_1, x_33);
x_35 = lean_io_error_to_string(x_30);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_2);
x_40 = lean_array_push(x_2, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_readTraceFile(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_1);
x_4 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_5 = l_Lake_BuildMetadata_toJson(x_2);
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_5, x_6);
x_8 = l_IO_FS_writeFile(x_1, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildMetadata_writeFile(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_BuildMetadata_ofFetch(x_2, x_3);
x_6 = l_Lake_BuildMetadata_writeFile(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_6 = l_Lake_writeFetchTrace(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_7, x_5);
x_9 = l_Lake_BuildMetadata_writeFile(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeBuildTrace___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_8, x_6);
x_10 = l_Lake_BuildMetadata_writeFile(x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeBuildTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_OutputStatus_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_outOfDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_outOfDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_mtimeUpToDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_hashUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_hashUpToDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_OutputStatus_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_OutputStatus_ctorIdx(x_1);
x_4 = l_Lake_OutputStatus_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqOutputStatus(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 2;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ofHashCheck(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ofMTimeCheck(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lake_instDecidableEqOutputStatus(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_isUpToDate(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 1;
x_3 = l_Lake_instDecidableEqOutputStatus(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_isCacheable(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_11 = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
x_12 = lean_box_uint64(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Option_instBEq_beq___redArg(x_11, x_13, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec_ref(x_2);
x_27 = lean_apply_2(x_1, x_3, lean_box(0));
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 2;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
x_10 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
x_13 = x_10;
x_14 = x_29;
goto block_28;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_29;
goto block_28;
}
block_28:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_unbox(x_11);
lean_dec(x_11);
x_17 = l_Lake_instDecidableEqOutputStatus(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_12);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_12);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_34; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_18 = x_15;
x_19 = x_34;
goto block_33;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_34;
goto block_33;
}
block_33:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_unbox(x_16);
lean_dec(x_16);
x_22 = l_Lake_instDecidableEqOutputStatus(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_box(x_23);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_24);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_17);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_29);
x_30 = x_18;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_17);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_checkHashUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_25; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
x_13 = x_5;
x_14 = x_25;
goto block_24;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget_borrowed(x_1, x_2);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = lean_array_push(x_8, x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_17);
x_18 = x_13;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_10);
x_18 = x_23;
goto block_22;
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_16;
x_5 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_16, x_17, x_11, x_7);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_10);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_19, x_20, x_11, x_7);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_64; 
x_14 = lean_ctor_get(x_5, 0);
x_64 = !lean_is_exclusive(x_5);
if (x_64 == 0)
{
x_15 = x_5;
x_16 = x_64;
goto block_63;
}
else
{
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = x_64;
goto block_63;
}
block_63:
{
uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get_uint64(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_14);
x_19 = lean_box_uint64(x_17);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_19);
x_20 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_60; 
x_21 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_20, x_6, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_ctor_get(x_21, 1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
x_24 = x_21;
x_25 = x_60;
goto block_59;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_26; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_31 = 0;
x_32 = lean_unbox(x_22);
x_33 = l_Lake_instDecidableEqOutputStatus(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_58; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get(x_23, 1);
x_38 = lean_ctor_get(x_23, 2);
x_58 = !lean_is_exclusive(x_23);
if (x_58 == 0)
{
x_39 = x_23;
x_40 = x_58;
goto block_57;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_34);
lean_dec(x_23);
x_39 = lean_box(0);
x_40 = x_58;
goto block_57;
}
block_57:
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_41 = 1;
x_42 = l_Lake_JobAction_merge(x_35, x_41);
if (x_40 == 0)
{
x_43 = x_39;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_56, 0, x_34);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_36);
x_43 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_44; 
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_42);
x_44 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_18, x_7, x_8, x_9, x_10, x_11, x_43);
lean_dec_ref(x_18);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_26 = x_45;
goto block_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_del_object(x_24);
lean_dec(x_22);
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
x_48 = x_44;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
}
else
{
lean_dec_ref(x_18);
x_26 = x_23;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_26);
x_27 = x_24;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_11, 0);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*2);
if (x_66 == 0)
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_12);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 0;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_74 = 1;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_12);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_33; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_17 = x_14;
x_18 = x_33;
goto block_32;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_33;
goto block_32;
}
block_32:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_unbox(x_15);
lean_dec(x_15);
x_21 = l_Lake_instDecidableEqOutputStatus(x_20, x_19);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_box(x_22);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_16);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_box(x_27);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_28);
x_29 = x_17;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_16);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
x_36 = x_14;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_34; 
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_18 = x_15;
x_19 = x_34;
goto block_33;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_34;
goto block_33;
}
block_33:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_unbox(x_16);
lean_dec(x_16);
x_22 = l_Lake_instDecidableEqOutputStatus(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_box(x_23);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_24);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_17);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_29);
x_30 = x_18;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_17);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
x_37 = x_15;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_24; uint64_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_33; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint64(x_24, sizeof(void*)*3);
x_26 = lean_ctor_get(x_24, 2);
x_27 = lean_ctor_get_uint8(x_24, sizeof(void*)*3 + 8);
x_28 = lean_uint64_dec_eq(x_25, x_1);
if (x_28 == 0)
{
x_5 = x_3;
goto block_23;
}
else
{
if (x_27 == 0)
{
goto block_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_array_get_size(x_26);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_71, x_72);
if (x_73 == 0)
{
goto block_70;
}
else
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_87; 
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_77 = lean_ctor_get(x_3, 1);
x_78 = lean_ctor_get(x_3, 2);
x_87 = !lean_is_exclusive(x_3);
if (x_87 == 0)
{
x_79 = x_3;
x_80 = x_87;
goto block_86;
}
else
{
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_74);
lean_dec(x_3);
x_79 = lean_box(0);
x_80 = x_87;
goto block_86;
}
block_86:
{
uint8_t x_81; uint8_t x_82; lean_object* x_83; 
x_81 = 2;
x_82 = l_Lake_JobAction_merge(x_75, x_81);
if (x_80 == 0)
{
x_83 = x_79;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_78);
lean_ctor_set_uint8(x_85, sizeof(void*)*3 + 1, x_76);
x_83 = x_85;
goto block_84;
}
block_84:
{
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_82);
x_29 = x_83;
goto block_32;
}
}
}
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
block_44:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_29 = x_34;
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
x_37 = x_33;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
block_70:
{
lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_69; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_69 = !lean_is_exclusive(x_3);
if (x_69 == 0)
{
x_50 = x_3;
x_51 = x_69;
goto block_68;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_45);
lean_dec(x_3);
x_50 = lean_box(0);
x_51 = x_69;
goto block_68;
}
block_68:
{
uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_52 = 1;
x_53 = l_Lake_JobAction_merge(x_46, x_52);
if (x_51 == 0)
{
x_54 = x_50;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_48);
lean_ctor_set(x_67, 2, x_49);
lean_ctor_set_uint8(x_67, sizeof(void*)*3 + 1, x_47);
x_54 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_26);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
x_29 = x_54;
goto block_32;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_box(0);
x_59 = lean_nat_dec_le(x_56, x_56);
if (x_59 == 0)
{
if (x_57 == 0)
{
x_29 = x_54;
goto block_32;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_56);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_26, x_60, x_61, x_58, x_54);
x_33 = x_62;
goto block_44;
}
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_56);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_26, x_63, x_64, x_58, x_54);
x_33 = x_65;
goto block_44;
}
}
}
}
}
}
else
{
x_5 = x_3;
goto block_23;
}
block_23:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_22; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
x_11 = x_5;
x_12 = x_22;
goto block_21;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 2;
x_14 = l_Lake_JobAction_merge(x_7, x_13);
if (x_12 == 0)
{
x_15 = x_11;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_8);
x_15 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_6 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_5, x_2, x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_11 = l_Lake_SavedTrace_replayOrFetchIfUpToDate(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Hash_hex(x_3);
x_9 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_4);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_Hash_hex(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToOutputJsonArtifact___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_5 = lean_io_mono_ms_now();
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_11 = x_3;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_15);
x_16 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_8);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_139; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_31 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_32 = lean_ctor_get(x_11, 1);
x_33 = lean_ctor_get(x_11, 2);
x_139 = !lean_is_exclusive(x_11);
if (x_139 == 0)
{
x_34 = x_11;
x_35 = x_139;
goto block_138;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_29);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = x_139;
goto block_138;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
x_23 = lean_array_get_size(x_17);
x_24 = lean_array_push(x_17, x_22);
x_25 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
block_138:
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 2);
x_37 = l_Lake_JobAction_merge(x_30, x_5);
x_38 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(x_3);
x_39 = l_System_FilePath_addExtension(x_3, x_38);
if (x_36 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_io_mono_ms_now();
lean_inc_ref(x_29);
if (x_35 == 0)
{
x_41 = x_34;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_122, 0, x_29);
lean_ctor_set(x_122, 1, x_32);
lean_ctor_set(x_122, 2, x_33);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 1, x_31);
x_41 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_37);
x_42 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_41, lean_box(0));
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec_ref(x_42);
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get_uint8(x_49, sizeof(void*)*3);
x_53 = lean_ctor_get_uint8(x_49, sizeof(void*)*3 + 1);
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 2);
x_56 = lean_array_get_size(x_29);
lean_dec_ref(x_29);
x_57 = lean_array_get_size(x_51);
x_58 = l_Array_extract___redArg(x_51, x_56, x_57);
lean_inc(x_50);
x_59 = lean_apply_1(x_1, x_50);
x_60 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_59, x_58);
x_61 = l_Lake_BuildMetadata_writeFile(x_3, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; uint8_t x_102; 
x_102 = !lean_is_exclusive(x_61);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_61, 0);
lean_dec(x_103);
x_62 = x_61;
x_63 = x_102;
goto block_101;
}
else
{
lean_dec(x_61);
x_62 = lean_box(0);
x_63 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_64; 
x_64 = l_Lake_removeFileIfExists(x_39);
lean_dec_ref(x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_84; 
x_84 = !lean_is_exclusive(x_64);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_64, 0);
lean_dec(x_85);
x_65 = x_64;
x_66 = x_84;
goto block_83;
}
else
{
lean_dec(x_64);
x_65 = lean_box(0);
x_66 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_67; 
lean_inc(x_50);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_50);
x_67 = x_65;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_50);
x_67 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_68; 
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_67);
x_68 = x_62;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_67);
x_68 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
x_69 = l_Lake_buildAction___redArg___lam__0(x_40, x_68, x_49);
lean_dec_ref(x_68);
lean_dec(x_40);
x_70 = lean_ctor_get(x_69, 1);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_69, 0);
lean_dec(x_78);
x_71 = x_69;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_50);
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
}
else
{
lean_object* x_86; uint8_t x_87; uint8_t x_97; 
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_51);
lean_del_object(x_62);
lean_dec(x_50);
x_97 = !lean_is_exclusive(x_49);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_49, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_49, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_49, 0);
lean_dec(x_100);
x_86 = x_49;
x_87 = x_97;
goto block_96;
}
else
{
lean_dec(x_49);
x_86 = lean_box(0);
x_87 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_64, 0);
lean_inc(x_88);
lean_dec_ref(x_64);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_push(x_51, x_91);
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_92);
x_93 = x_86;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_54);
lean_ctor_set(x_95, 2, x_55);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_52);
lean_ctor_set_uint8(x_95, sizeof(void*)*3 + 1, x_53);
x_93 = x_95;
goto block_94;
}
block_94:
{
x_43 = x_57;
x_44 = x_93;
goto block_48;
}
}
}
}
}
else
{
lean_object* x_104; uint8_t x_105; uint8_t x_115; 
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_39);
x_115 = !lean_is_exclusive(x_49);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_49, 2);
lean_dec(x_116);
x_117 = lean_ctor_get(x_49, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_49, 0);
lean_dec(x_118);
x_104 = x_49;
x_105 = x_115;
goto block_114;
}
else
{
lean_dec(x_49);
x_104 = lean_box(0);
x_105 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_61, 0);
lean_inc(x_106);
lean_dec_ref(x_61);
x_107 = lean_io_error_to_string(x_106);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_push(x_51, x_109);
if (x_105 == 0)
{
lean_ctor_set(x_104, 0, x_110);
x_111 = x_104;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_54);
lean_ctor_set(x_113, 2, x_55);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_52);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 1, x_53);
x_111 = x_113;
goto block_112;
}
block_112:
{
x_43 = x_57;
x_44 = x_111;
goto block_48;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_39);
lean_dec_ref(x_29);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_119 = lean_ctor_get(x_42, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_42, 1);
lean_inc(x_120);
lean_dec_ref(x_42);
x_43 = x_119;
x_44 = x_120;
goto block_48;
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
x_46 = l_Lake_buildAction___redArg___lam__0(x_40, x_45, x_44);
lean_dec(x_40);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_13 = x_43;
x_14 = x_47;
goto block_16;
}
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_123 = l_System_FilePath_pathExists(x_3);
lean_dec_ref(x_3);
if (x_123 == 0)
{
lean_dec_ref(x_39);
lean_del_object(x_34);
x_17 = x_29;
x_18 = x_37;
x_19 = x_36;
x_20 = x_32;
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_box(0);
x_125 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
x_126 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_124, x_125);
x_127 = l_Lake_BuildMetadata_writeFile(x_39, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_dec_ref(x_127);
lean_del_object(x_34);
x_17 = x_29;
x_18 = x_37;
x_19 = x_36;
x_20 = x_32;
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_io_error_to_string(x_128);
x_130 = 3;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_array_get_size(x_29);
x_133 = lean_array_push(x_29, x_131);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_133);
x_134 = x_34;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_32);
lean_ctor_set(x_137, 2, x_33);
x_134 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_135; 
lean_ctor_set_uint8(x_134, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_134, sizeof(void*)*3 + 1, x_36);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildAction___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildAction___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildAction(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_88; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_ctor_get(x_14, 2);
x_88 = !lean_is_exclusive(x_14);
if (x_88 == 0)
{
x_21 = x_14;
x_22 = x_88;
goto block_87;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_23; 
lean_inc_ref(x_5);
x_23 = l_Lake_readTraceFile(x_5, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_25);
x_26 = x_21;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_74, 0, x_25);
lean_ctor_set(x_74, 1, x_19);
lean_ctor_set(x_74, 2, x_20);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_74, sizeof(void*)*3 + 1, x_18);
x_26 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_27; 
x_27 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_63; 
x_28 = lean_ctor_get(x_27, 0);
x_29 = lean_ctor_get(x_27, 1);
x_63 = !lean_is_exclusive(x_27);
if (x_63 == 0)
{
x_30 = x_27;
x_31 = x_63;
goto block_62;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = x_63;
goto block_62;
}
block_62:
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; 
x_32 = 0;
x_33 = lean_unbox(x_28);
lean_dec(x_28);
x_34 = l_Lake_instDecidableEqOutputStatus(x_33, x_32);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_35 = 1;
x_36 = lean_box(x_35);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_36);
x_37 = x_30;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_29);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_del_object(x_30);
x_40 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_41 = l_Lake_buildAction___redArg(x_40, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_51; 
x_42 = lean_ctor_get(x_41, 1);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_41, 0);
lean_dec(x_52);
x_43 = x_41;
x_44 = x_51;
goto block_50;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_box(x_45);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_46);
x_47 = x_43;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_42);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
x_55 = x_41;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_64 = lean_ctor_get(x_27, 0);
x_65 = lean_ctor_get(x_27, 1);
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
x_66 = x_27;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_27);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_86; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_23, 0);
x_76 = lean_ctor_get(x_23, 1);
x_86 = !lean_is_exclusive(x_23);
if (x_86 == 0)
{
x_77 = x_23;
x_78 = x_86;
goto block_85;
}
else
{
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_23);
x_77 = lean_box(0);
x_78 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_79; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_76);
x_79 = x_21;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_19);
lean_ctor_set(x_84, 2, x_20);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_84, sizeof(void*)*3 + 1, x_18);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_78 == 0)
{
lean_ctor_set(x_77, 1, x_79);
x_80 = x_77;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_79);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
x_17 = l_Lake_buildUnlessUpToDate_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_89; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_15, 2);
x_89 = !lean_is_exclusive(x_15);
if (x_89 == 0)
{
x_22 = x_15;
x_23 = x_89;
goto block_88;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_24; 
lean_inc_ref(x_6);
x_24 = l_Lake_readTraceFile(x_6, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_26);
x_27 = x_22;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_75, 0, x_26);
lean_ctor_set(x_75, 1, x_20);
lean_ctor_set(x_75, 2, x_21);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_75, sizeof(void*)*3 + 1, x_19);
x_27 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_28; 
x_28 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_64; 
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
x_64 = !lean_is_exclusive(x_28);
if (x_64 == 0)
{
x_31 = x_28;
x_32 = x_64;
goto block_63;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_33 = 0;
x_34 = lean_unbox(x_29);
lean_dec(x_29);
x_35 = l_Lake_instDecidableEqOutputStatus(x_34, x_33);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_36 = 1;
x_37 = lean_box(x_36);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_37);
x_38 = x_31;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_30);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_del_object(x_31);
x_41 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_42 = l_Lake_buildAction___redArg(x_41, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_52; 
x_43 = lean_ctor_get(x_42, 1);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_42, 0);
lean_dec(x_53);
x_44 = x_42;
x_45 = x_52;
goto block_51;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_52;
goto block_51;
}
block_51:
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = 0;
x_47 = lean_box(x_46);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_47);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_43);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
x_54 = lean_ctor_get(x_42, 0);
x_55 = lean_ctor_get(x_42, 1);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
x_56 = x_42;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_42);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_65 = lean_ctor_get(x_28, 0);
x_66 = lean_ctor_get(x_28, 1);
x_73 = !lean_is_exclusive(x_28);
if (x_73 == 0)
{
x_67 = x_28;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_28);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_87; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_24, 0);
x_77 = lean_ctor_get(x_24, 1);
x_87 = !lean_is_exclusive(x_24);
if (x_87 == 0)
{
x_78 = x_24;
x_79 = x_87;
goto block_86;
}
else
{
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_24);
x_78 = lean_box(0);
x_79 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_80; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_77);
x_80 = x_22;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_20);
lean_ctor_set(x_85, 2, x_21);
lean_ctor_set_uint8(x_85, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_85, sizeof(void*)*3 + 1, x_19);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_79 == 0)
{
lean_ctor_set(x_78, 1, x_80);
x_81 = x_78;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildUnlessUpToDate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_62; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
x_25 = x_14;
x_26 = x_62;
goto block_61;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_20);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = x_62;
goto block_61;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
block_61:
{
lean_object* x_27; 
lean_inc_ref(x_5);
x_27 = l_Lake_readTraceFile(x_5, x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_55, 0, x_29);
lean_ctor_set(x_55, 1, x_23);
lean_ctor_set(x_55, 2, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_22);
x_30 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_31; 
x_31 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_51; 
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
x_34 = x_31;
x_35 = x_51;
goto block_50;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_36; lean_object* x_37; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_36 = lean_box(0);
x_42 = 0;
x_43 = lean_unbox(x_32);
lean_dec(x_32);
x_44 = l_Lake_instDecidableEqOutputStatus(x_43, x_42);
if (x_44 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_37 = x_33;
goto block_41;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_46 = l_Lake_buildAction___redArg(x_45, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_37 = x_47;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_del_object(x_34);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec_ref(x_46);
x_16 = x_48;
x_17 = x_49;
goto block_19;
}
}
block_41:
{
lean_object* x_38; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_37);
lean_ctor_set(x_34, 0, x_36);
x_38 = x_34;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_52 = lean_ctor_get(x_31, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_dec_ref(x_31);
x_16 = x_52;
x_17 = x_53;
goto block_19;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_27, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_57);
x_58 = x_25;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_23);
lean_ctor_set(x_60, 2, x_24);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_60, sizeof(void*)*3 + 1, x_22);
x_58 = x_60;
goto block_59;
}
block_59:
{
x_16 = x_56;
x_17 = x_58;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
x_17 = l_Lake_buildUnlessUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_63; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_15, 2);
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
x_26 = x_15;
x_27 = x_63;
goto block_62;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_21);
lean_dec(x_15);
x_26 = lean_box(0);
x_27 = x_63;
goto block_62;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
block_62:
{
lean_object* x_28; 
lean_inc_ref(x_6);
x_28 = l_Lake_readTraceFile(x_6, x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_30);
x_31 = x_26;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_56, 0, x_30);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_23);
x_31 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_32; 
x_32 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_52; 
x_33 = lean_ctor_get(x_32, 0);
x_34 = lean_ctor_get(x_32, 1);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
x_35 = x_32;
x_36 = x_52;
goto block_51;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_37; lean_object* x_38; uint8_t x_43; uint8_t x_44; uint8_t x_45; 
x_37 = lean_box(0);
x_43 = 0;
x_44 = lean_unbox(x_33);
lean_dec(x_33);
x_45 = l_Lake_instDecidableEqOutputStatus(x_44, x_43);
if (x_45 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_38 = x_34;
goto block_42;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_47 = l_Lake_buildAction___redArg(x_46, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_34);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_38 = x_48;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_del_object(x_35);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_17 = x_49;
x_18 = x_50;
goto block_20;
}
}
block_42:
{
lean_object* x_39; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_38);
lean_ctor_set(x_35, 0, x_37);
x_39 = x_35;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_dec_ref(x_32);
x_17 = x_53;
x_18 = x_54;
goto block_20;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_dec_ref(x_28);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_58);
x_59 = x_26;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_24);
lean_ctor_set(x_61, 2, x_25);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_61, sizeof(void*)*3 + 1, x_23);
x_59 = x_61;
goto block_60;
}
block_60:
{
x_17 = x_57;
x_18 = x_59;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildUnlessUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = ((lean_object*)(l_Lake_writeFileHash___closed__0));
x_5 = lean_string_append(x_1, x_4);
lean_inc_ref(x_5);
x_6 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_6);
x_7 = l_Lake_Hash_hex(x_2);
x_8 = l_IO_FS_writeFile(x_5, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_8;
}
else
{
lean_dec_ref(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Lake_writeFileHash(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; 
if (x_2 == 0)
{
lean_object* x_17; 
x_17 = l_Lake_computeBinFileHash(x_1);
x_4 = x_17;
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = l_Lake_computeTextFileHash(x_1);
x_4 = x_18;
goto block_16;
}
block_16:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l_Lake_writeFileHash(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
x_9 = x_4;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_cacheFileHash(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(l_Lake_writeFileHash___closed__0));
x_4 = lean_string_append(x_1, x_3);
x_5 = l_Lake_removeFileIfExists(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_clearFileHash(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_48; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 1);
x_8 = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(x_1);
x_9 = lean_string_append(x_1, x_8);
if (x_7 == 0)
{
x_48 = x_4;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = l_Lake_Hash_load_x3f(x_9);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
else
{
lean_dec(x_62);
x_48 = x_4;
goto block_61;
}
}
block_47:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_9);
x_17 = l_Lake_createParentDirs(x_9);
if (lean_obj_tag(x_17) == 0)
{
uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_17);
x_18 = lean_unbox_uint64(x_16);
x_19 = l_Lake_Hash_hex(x_18);
x_20 = l_IO_FS_writeFile(x_9, x_19);
lean_dec_ref(x_19);
lean_dec_ref(x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_20);
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_io_error_to_string(x_23);
x_25 = 3;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_get_size(x_12);
x_28 = lean_array_push(x_12, x_26);
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_11);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_dec_ref(x_9);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec_ref(x_17);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_12);
x_36 = lean_array_push(x_12, x_34);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_11);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_9);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec_ref(x_15);
x_40 = lean_io_error_to_string(x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_12);
x_44 = lean_array_push(x_12, x_42);
x_45 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_13);
lean_ctor_set(x_45, 2, x_11);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 1, x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_61:
{
if (x_2 == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_51 = lean_ctor_get_uint8(x_48, sizeof(void*)*3 + 1);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
lean_dec_ref(x_48);
x_54 = l_Lake_computeBinFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_50;
x_11 = x_53;
x_12 = x_49;
x_13 = x_52;
x_14 = x_51;
x_15 = x_54;
goto block_47;
}
else
{
lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_57 = lean_ctor_get_uint8(x_48, sizeof(void*)*3 + 1);
x_58 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_48, 2);
lean_inc(x_59);
lean_dec_ref(x_48);
x_60 = l_Lake_computeTextFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_56;
x_11 = x_59;
x_12 = x_55;
x_13 = x_58;
x_14 = x_57;
x_15 = x_60;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileHash(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_1);
x_6 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_45; 
x_7 = lean_ctor_get(x_6, 1);
x_8 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_9 = x_6;
x_10 = x_45;
goto block_44;
}
else
{
lean_inc(x_7);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_io_metadata(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_20 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_21);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_20);
x_22 = x_9;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_7);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_40; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_7, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_7, 0);
lean_dec(x_43);
x_25 = x_7;
x_26 = x_40;
goto block_39;
}
else
{
lean_dec(x_7);
x_25 = lean_box(0);
x_26 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_11);
x_32 = lean_array_push(x_11, x_30);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_32);
x_33 = x_25;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_14);
lean_ctor_set(x_38, 2, x_15);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_13);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_33);
lean_ctor_set(x_9, 0, x_31);
x_34 = x_9;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
x_48 = x_6;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lake_fetchFileTrace___redArg(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileTrace___redArg(x_1, x_2, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileTrace(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_5 = lean_io_mono_ms_now();
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_11 = x_3;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_15);
x_16 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_8);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_156; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_31 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_32 = lean_ctor_get(x_11, 1);
x_33 = lean_ctor_get(x_11, 2);
x_156 = !lean_is_exclusive(x_11);
if (x_156 == 0)
{
x_34 = x_11;
x_35 = x_156;
goto block_155;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_29);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = x_156;
goto block_155;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
x_23 = lean_array_get_size(x_17);
x_24 = lean_array_push(x_17, x_22);
x_25 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
block_155:
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get_uint8(x_28, sizeof(void*)*2 + 2);
x_37 = l_Lake_JobAction_merge(x_30, x_6);
x_38 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(x_5);
x_39 = l_System_FilePath_addExtension(x_5, x_38);
if (x_36 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_io_mono_ms_now();
lean_inc_ref(x_29);
if (x_35 == 0)
{
x_41 = x_34;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_139, 0, x_29);
lean_ctor_set(x_139, 1, x_32);
lean_ctor_set(x_139, 2, x_33);
lean_ctor_set_uint8(x_139, sizeof(void*)*3 + 1, x_31);
x_41 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_37);
x_42 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_41, lean_box(0));
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec_ref(x_42);
x_50 = lean_ctor_get(x_49, 0);
x_51 = lean_ctor_get_uint8(x_49, sizeof(void*)*3);
x_52 = lean_ctor_get_uint8(x_49, sizeof(void*)*3 + 1);
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 2);
x_55 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_array_get_size(x_29);
lean_dec_ref(x_29);
x_58 = lean_array_get_size(x_50);
x_59 = l_Array_extract___redArg(x_50, x_57, x_58);
x_60 = lean_box(0);
x_61 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_60, x_59);
x_62 = l_Lake_BuildMetadata_writeFile(x_5, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; uint8_t x_103; 
x_103 = !lean_is_exclusive(x_62);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_62, 0);
lean_dec(x_104);
x_63 = x_62;
x_64 = x_103;
goto block_102;
}
else
{
lean_dec(x_62);
x_63 = lean_box(0);
x_64 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_65; 
x_65 = l_Lake_removeFileIfExists(x_39);
lean_dec_ref(x_39);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; uint8_t x_85; 
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_65, 0);
lean_dec(x_86);
x_66 = x_65;
x_67 = x_85;
goto block_84;
}
else
{
lean_dec(x_65);
x_66 = lean_box(0);
x_67 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_68; 
lean_inc(x_56);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_56);
x_68 = x_66;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_56);
x_68 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_69; 
if (x_64 == 0)
{
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_68);
x_69 = x_63;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_68);
x_69 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_70 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_40, x_69, x_49);
lean_dec_ref(x_69);
lean_dec(x_40);
x_71 = lean_ctor_get(x_70, 1);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_70, 0);
lean_dec(x_79);
x_72 = x_70;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
lean_ctor_set(x_72, 0, x_56);
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_56);
lean_ctor_set(x_76, 1, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_98; 
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_50);
lean_del_object(x_63);
lean_dec(x_56);
x_98 = !lean_is_exclusive(x_49);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_49, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_49, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_49, 0);
lean_dec(x_101);
x_87 = x_49;
x_88 = x_98;
goto block_97;
}
else
{
lean_dec(x_49);
x_87 = lean_box(0);
x_88 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_65, 0);
lean_inc(x_89);
lean_dec_ref(x_65);
x_90 = lean_io_error_to_string(x_89);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_push(x_50, x_92);
if (x_88 == 0)
{
lean_ctor_set(x_87, 0, x_93);
x_94 = x_87;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_53);
lean_ctor_set(x_96, 2, x_54);
lean_ctor_set_uint8(x_96, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_96, sizeof(void*)*3 + 1, x_52);
x_94 = x_96;
goto block_95;
}
block_95:
{
x_43 = x_58;
x_44 = x_94;
goto block_48;
}
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_116; 
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_50);
lean_dec(x_56);
lean_dec_ref(x_39);
x_116 = !lean_is_exclusive(x_49);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_49, 2);
lean_dec(x_117);
x_118 = lean_ctor_get(x_49, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_49, 0);
lean_dec(x_119);
x_105 = x_49;
x_106 = x_116;
goto block_115;
}
else
{
lean_dec(x_49);
x_105 = lean_box(0);
x_106 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_62, 0);
lean_inc(x_107);
lean_dec_ref(x_62);
x_108 = lean_io_error_to_string(x_107);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_50, x_110);
if (x_106 == 0)
{
lean_ctor_set(x_105, 0, x_111);
x_112 = x_105;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_53);
lean_ctor_set(x_114, 2, x_54);
lean_ctor_set_uint8(x_114, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_114, sizeof(void*)*3 + 1, x_52);
x_112 = x_114;
goto block_113;
}
block_113:
{
x_43 = x_58;
x_44 = x_112;
goto block_48;
}
}
}
}
else
{
lean_object* x_120; uint8_t x_121; uint8_t x_132; 
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_50);
lean_dec_ref(x_39);
lean_dec_ref(x_29);
lean_dec_ref(x_5);
x_132 = !lean_is_exclusive(x_49);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_49, 2);
lean_dec(x_133);
x_134 = lean_ctor_get(x_49, 1);
lean_dec(x_134);
x_135 = lean_ctor_get(x_49, 0);
lean_dec(x_135);
x_120 = x_49;
x_121 = x_132;
goto block_131;
}
else
{
lean_dec(x_49);
x_120 = lean_box(0);
x_121 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_55, 0);
lean_inc(x_122);
lean_dec_ref(x_55);
x_123 = lean_io_error_to_string(x_122);
x_124 = 3;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_get_size(x_50);
x_127 = lean_array_push(x_50, x_125);
if (x_121 == 0)
{
lean_ctor_set(x_120, 0, x_127);
x_128 = x_120;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_53);
lean_ctor_set(x_130, 2, x_54);
lean_ctor_set_uint8(x_130, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_130, sizeof(void*)*3 + 1, x_52);
x_128 = x_130;
goto block_129;
}
block_129:
{
x_43 = x_126;
x_44 = x_128;
goto block_48;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_39);
lean_dec_ref(x_29);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_136 = lean_ctor_get(x_42, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_42, 1);
lean_inc(x_137);
lean_dec_ref(x_42);
x_43 = x_136;
x_44 = x_137;
goto block_48;
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
x_46 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_40, x_45, x_44);
lean_dec(x_40);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_13 = x_43;
x_14 = x_47;
goto block_16;
}
}
}
else
{
uint8_t x_140; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = l_System_FilePath_pathExists(x_5);
lean_dec_ref(x_5);
if (x_140 == 0)
{
lean_dec_ref(x_39);
lean_del_object(x_34);
x_17 = x_29;
x_18 = x_37;
x_19 = x_36;
x_20 = x_32;
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_box(0);
x_142 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
x_143 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_141, x_142);
x_144 = l_Lake_BuildMetadata_writeFile(x_39, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_dec_ref(x_144);
lean_del_object(x_34);
x_17 = x_29;
x_18 = x_37;
x_19 = x_36;
x_20 = x_32;
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_io_error_to_string(x_145);
x_147 = 3;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_get_size(x_29);
x_150 = lean_array_push(x_29, x_148);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_150);
x_151 = x_34;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_32);
lean_ctor_set(x_154, 2, x_33);
x_151 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_152; 
lean_ctor_set_uint8(x_151, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_151, sizeof(void*)*3 + 1, x_36);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_metadata(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_IO_FS_instOrdSystemTime_ord(x_2, x_6);
lean_dec_ref(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_4);
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox_uint64(x_6);
x_9 = lean_unbox_uint64(x_7);
x_10 = lean_uint64_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_9 = lean_box_uint64(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(x_10, x_3);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_4);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = l_System_FilePath_pathExists(x_1);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 2;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_62; 
x_12 = lean_ctor_get(x_4, 0);
x_62 = !lean_is_exclusive(x_4);
if (x_62 == 0)
{
x_13 = x_4;
x_14 = x_62;
goto block_61;
}
else
{
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_62;
goto block_61;
}
block_61:
{
uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get_uint64(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_12);
x_17 = lean_box_uint64(x_15);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_17);
x_18 = x_13;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_17);
x_18 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_58; 
x_19 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_18, x_5, x_9, x_10);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
x_22 = x_19;
x_23 = x_58;
goto block_57;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_24; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = 0;
x_30 = lean_unbox(x_20);
x_31 = l_Lake_instDecidableEqOutputStatus(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_56; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get(x_21, 1);
x_36 = lean_ctor_get(x_21, 2);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
x_37 = x_21;
x_38 = x_56;
goto block_55;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_32);
lean_dec(x_21);
x_37 = lean_box(0);
x_38 = x_56;
goto block_55;
}
block_55:
{
uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_39 = 1;
x_40 = l_Lake_JobAction_merge(x_33, x_39);
if (x_38 == 0)
{
x_41 = x_37;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_35);
lean_ctor_set(x_54, 2, x_36);
lean_ctor_set_uint8(x_54, sizeof(void*)*3 + 1, x_34);
x_41 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_42; 
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_16, x_1, x_6, x_7, x_8, x_9, x_41);
lean_dec_ref(x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_24 = x_43;
goto block_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_del_object(x_22);
lean_dec(x_20);
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
x_46 = x_42;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
else
{
lean_dec_ref(x_16);
x_24 = x_21;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_4);
x_63 = lean_ctor_get(x_9, 0);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*2);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_10);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_2, x_5);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_72 = 1;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_10);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_84; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_51 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_52 = lean_ctor_get(x_9, 1);
x_53 = lean_ctor_get(x_9, 2);
x_84 = !lean_is_exclusive(x_9);
if (x_84 == 0)
{
x_54 = x_9;
x_55 = x_84;
goto block_83;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_49);
lean_dec(x_9);
x_54 = lean_box(0);
x_55 = x_84;
goto block_83;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
block_48:
{
lean_object* x_16; 
x_16 = l_Lake_fetchFileTrace___redArg(x_1, x_3, x_8, x_15);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_38; 
x_17 = lean_ctor_get(x_16, 1);
x_18 = lean_ctor_get(x_16, 0);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
x_19 = x_16;
x_20 = x_38;
goto block_37;
}
else
{
lean_inc(x_17);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get(x_17, 2);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_17, 1);
lean_dec(x_36);
x_25 = x_17;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_inc(x_21);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_18);
x_28 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_18);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*3 + 1, x_23);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_28);
lean_ctor_set(x_19, 0, x_27);
x_29 = x_19;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_41 = x_16;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
block_83:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_57 = lean_string_append(x_1, x_56);
lean_inc_ref(x_57);
x_58 = l_Lake_readTraceFile(x_57, x_49);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_52, 2);
lean_inc_ref(x_52);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_60);
x_62 = x_54;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_77, 0, x_60);
lean_ctor_set(x_77, 1, x_52);
lean_ctor_set(x_77, 2, x_53);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_50);
lean_ctor_set_uint8(x_77, sizeof(void*)*3 + 1, x_51);
x_62 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_63; 
x_63 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_52, x_59, x_61, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = 0;
x_67 = lean_unbox(x_64);
lean_dec(x_64);
x_68 = l_Lake_instDecidableEqOutputStatus(x_67, x_66);
if (x_68 == 0)
{
lean_dec_ref(x_57);
lean_dec_ref(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_15 = x_65;
goto block_48;
}
else
{
uint8_t x_69; lean_object* x_70; 
x_69 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_70 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_2, x_1, x_4, x_52, x_57, x_69, x_5, x_6, x_7, x_8, x_65);
lean_dec_ref(x_52);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
x_15 = x_71;
goto block_48;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec_ref(x_70);
x_11 = x_72;
x_12 = x_73;
goto block_14;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_57);
lean_dec_ref(x_52);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_dec_ref(x_63);
x_11 = x_74;
x_12 = x_75;
goto block_14;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_57);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_58, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
lean_dec_ref(x_58);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_79);
x_80 = x_54;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_52);
lean_ctor_set(x_82, 2, x_53);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_50);
lean_ctor_set_uint8(x_82, sizeof(void*)*3 + 1, x_51);
x_80 = x_82;
goto block_81;
}
block_81:
{
x_11 = x_78;
x_12 = x_80;
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lake_writeFileHash(x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = lean_io_metadata(x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
x_14 = x_19;
goto block_15;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_17);
x_20 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_14 = x_20;
goto block_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_16, 0);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_22 = x_16;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_15:
{
if (x_4 == 0)
{
x_8 = x_14;
x_9 = x_5;
goto block_13;
}
else
{
lean_dec_ref(x_5);
lean_inc_ref(x_1);
x_8 = x_14;
x_9 = x_1;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_9 = lean_unbox(x_4);
x_10 = l_Lake_Cache_saveArtifact___lam__0(x_1, x_8, x_3, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lake_writeFileHash(x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = lean_io_metadata(x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
x_14 = x_19;
goto block_15;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_17);
x_20 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_14 = x_20;
goto block_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_16, 0);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_22 = x_16;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_15:
{
if (x_4 == 0)
{
x_8 = x_14;
x_9 = x_5;
goto block_13;
}
else
{
lean_dec_ref(x_5);
lean_inc_ref(x_1);
x_8 = x_14;
x_9 = x_1;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_9 = lean_unbox(x_4);
x_10 = l_Lake_Cache_saveArtifact___lam__1(x_1, x_8, x_3, x_9, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__2));
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; lean_object* x_15; uint8_t x_27; 
x_27 = 1;
if (x_4 == 0)
{
lean_object* x_28; 
x_28 = l_IO_FS_readBinFile(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lake_Hash_nil;
x_31 = lean_byte_array_hash(x_29);
x_32 = lean_uint64_mix_hash(x_30, x_31);
lean_inc_ref(x_3);
x_33 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set_uint64(x_33, sizeof(void*)*1, x_32);
x_34 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
x_35 = l_System_FilePath_join(x_1, x_34);
x_57 = lean_string_utf8_byte_size(x_3);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lake_Hash_hex(x_32);
x_61 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_3);
lean_dec_ref(x_3);
x_36 = x_63;
goto block_56;
}
else
{
lean_object* x_64; 
lean_dec_ref(x_3);
x_64 = l_Lake_Hash_hex(x_32);
x_36 = x_64;
goto block_56;
}
block_56:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_37, 0, x_27);
lean_ctor_set_uint8(x_37, 1, x_4);
lean_ctor_set_uint8(x_37, 2, x_5);
lean_inc_ref_n(x_37, 2);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_IO_setAccessRights(x_2, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_39);
x_40 = l_Lake_joinRelative(x_35, x_36);
x_41 = l_System_FilePath_pathExists(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc_ref(x_40);
x_42 = l_Lake_createParentDirs(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec_ref(x_42);
x_43 = lean_io_hard_link(x_2, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_43);
lean_dec_ref(x_38);
lean_dec(x_29);
x_44 = lean_box(0);
x_45 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_32, x_33, x_6, x_40, x_44);
x_15 = x_45;
goto block_26;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_43);
x_46 = l_IO_FS_writeBinFile(x_40, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_46);
x_47 = l_IO_setAccessRights(x_40, x_38);
lean_dec_ref(x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_32, x_33, x_6, x_40, x_48);
x_15 = x_49;
goto block_26;
}
else
{
lean_object* x_50; 
lean_dec_ref(x_40);
lean_dec_ref(x_33);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec_ref(x_47);
x_8 = x_50;
goto block_14;
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_33);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec_ref(x_46);
x_8 = x_51;
goto block_14;
}
}
}
else
{
lean_object* x_52; 
lean_dec_ref(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_33);
lean_dec(x_29);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec_ref(x_42);
x_8 = x_52;
goto block_14;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_38);
lean_dec(x_29);
x_53 = lean_box(0);
x_54 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_32, x_33, x_6, x_40, x_53);
x_15 = x_54;
goto block_26;
}
}
else
{
lean_object* x_55; 
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_33);
lean_dec(x_29);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_39, 0);
lean_inc(x_55);
lean_dec_ref(x_39);
x_8 = x_55;
goto block_14;
}
}
}
else
{
lean_object* x_65; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
lean_dec_ref(x_28);
x_8 = x_65;
goto block_14;
}
}
else
{
lean_object* x_66; 
x_66 = l_IO_FS_readFile(x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_String_crlfToLf(x_67);
lean_dec(x_67);
x_69 = l_Lake_Hash_nil;
x_70 = lean_string_hash(x_68);
x_71 = lean_uint64_mix_hash(x_69, x_70);
lean_inc_ref(x_3);
x_72 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_71);
x_73 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
x_74 = l_System_FilePath_join(x_1, x_73);
x_92 = lean_string_utf8_byte_size(x_3);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = l_Lake_Hash_hex(x_71);
x_96 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_string_append(x_97, x_3);
lean_dec_ref(x_3);
x_75 = x_98;
goto block_91;
}
else
{
lean_object* x_99; 
lean_dec_ref(x_3);
x_99 = l_Lake_Hash_hex(x_71);
x_75 = x_99;
goto block_91;
}
block_91:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_obj_once(&l_Lake_Cache_saveArtifact___closed__3, &l_Lake_Cache_saveArtifact___closed__3_once, _init_l_Lake_Cache_saveArtifact___closed__3);
x_77 = l_IO_setAccessRights(x_2, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_77);
x_78 = l_Lake_joinRelative(x_74, x_75);
x_79 = l_System_FilePath_pathExists(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_inc_ref(x_78);
x_80 = l_Lake_createParentDirs(x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec_ref(x_80);
x_81 = l_IO_FS_writeFile(x_78, x_68);
lean_dec_ref(x_68);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec_ref(x_81);
x_82 = l_IO_setAccessRights(x_78, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lake_Cache_saveArtifact___lam__1(x_2, x_71, x_72, x_6, x_78, x_83);
x_15 = x_84;
goto block_26;
}
else
{
lean_object* x_85; 
lean_dec_ref(x_78);
lean_dec_ref(x_72);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec_ref(x_82);
x_8 = x_85;
goto block_14;
}
}
else
{
lean_object* x_86; 
lean_dec_ref(x_78);
lean_dec_ref(x_72);
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec_ref(x_81);
x_8 = x_86;
goto block_14;
}
}
else
{
lean_object* x_87; 
lean_dec_ref(x_78);
lean_dec_ref(x_72);
lean_dec_ref(x_68);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
lean_dec_ref(x_80);
x_8 = x_87;
goto block_14;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_68);
x_88 = lean_box(0);
x_89 = l_Lake_Cache_saveArtifact___lam__1(x_2, x_71, x_72, x_6, x_78, x_88);
x_15 = x_89;
goto block_26;
}
}
else
{
lean_object* x_90; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_68);
lean_dec_ref(x_2);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
lean_dec_ref(x_77);
x_8 = x_90;
goto block_14;
}
}
}
else
{
lean_object* x_100; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_66, 0);
lean_inc(x_100);
lean_dec_ref(x_66);
x_8 = x_100;
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
x_10 = lean_io_error_to_string(x_8);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_mk_io_user_error(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_26:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
x_17 = x_15;
x_18 = x_24;
goto block_23;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec_ref(x_15);
x_8 = x_25;
goto block_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_4);
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lake_Cache_saveArtifact(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_cacheArtifact___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(x_3);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_10);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = l_Lake_cacheArtifact___redArg___lam__1(x_1, x_2, x_8, x_9, x_10, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
x_14 = lean_box(x_6);
x_15 = lean_box(x_7);
x_16 = lean_box(x_8);
x_17 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_5);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_2);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_1);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_6);
x_10 = lean_unbox(x_7);
x_11 = lean_unbox(x_8);
x_12 = l_Lake_cacheArtifact___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
x_15 = lean_box(x_7);
x_16 = lean_box(x_8);
x_17 = lean_box(x_9);
x_18 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_3);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_2);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_7);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_9);
x_13 = l_Lake_cacheArtifact(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0));
x_5 = lean_string_append(x_1, x_4);
x_6 = lean_string_append(x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getArtifacts_x3f___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_getArtifacts_x3f___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_32; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_48 = lean_ctor_get(x_9, 1);
x_49 = lean_ctor_get(x_48, 0);
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_51);
x_116 = lean_ctor_get(x_4, 6);
x_117 = lean_ctor_get(x_116, 25);
x_118 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_50, 6);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_49, 6);
x_211 = lean_ctor_get(x_210, 25);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = 0;
x_119 = x_212;
x_120 = x_10;
goto block_208;
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_unbox(x_213);
x_119 = x_214;
x_120 = x_10;
goto block_208;
}
}
else
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_209, 0);
x_216 = lean_unbox(x_215);
x_119 = x_216;
x_120 = x_10;
goto block_208;
}
}
else
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_ctor_get(x_117, 0);
x_218 = lean_unbox(x_217);
x_119 = x_218;
x_120 = x_10;
goto block_208;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_31:
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
x_23 = x_17;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_18);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Array_shrink___redArg(x_18, x_16);
lean_dec(x_16);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_20);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_12 = x_26;
goto block_15;
}
}
}
block_47:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_32, 0);
lean_dec(x_43);
x_35 = x_32;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec_ref(x_33);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_34);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec_ref(x_32);
x_12 = x_44;
goto block_15;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec_ref(x_32);
x_16 = x_45;
x_17 = x_46;
goto block_31;
}
}
block_102:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_60; uint64_t x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_3);
x_61 = lean_ctor_get_uint64(x_60, sizeof(void*)*3);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_uint64_dec_eq(x_61, x_2);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_12 = x_59;
goto block_15;
}
else
{
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_box(0);
lean_inc_ref(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc(x_64);
x_66 = lean_apply_10(x_1, x_64, x_65, x_65, x_54, x_55, x_56, x_57, x_58, x_59, lean_box(0));
if (lean_obj_tag(x_66) == 0)
{
if (x_52 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_box(0);
x_70 = l_Lake_getArtifacts_x3f___redArg___lam__1(x_67, x_69, x_54, x_55, x_56, x_57, x_58, x_68);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_32 = x_70;
goto block_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec_ref(x_66);
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
x_75 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 1);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_71, 2);
x_78 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_51, x_53, x_2, x_64, x_65, x_65);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_78);
x_79 = lean_box(0);
x_80 = l_Lake_getArtifacts_x3f___redArg___lam__1(x_72, x_79, x_54, x_55, x_56, x_57, x_58, x_71);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_32 = x_80;
goto block_47;
}
else
{
lean_object* x_81; uint8_t x_82; uint8_t x_96; 
lean_inc(x_77);
lean_inc_ref(x_76);
lean_inc_ref(x_73);
x_96 = !lean_is_exclusive(x_71);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_71, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_71, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_71, 0);
lean_dec(x_99);
x_81 = x_71;
x_82 = x_96;
goto block_95;
}
else
{
lean_dec(x_71);
x_81 = lean_box(0);
x_82 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec_ref(x_78);
x_84 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_85 = lean_io_error_to_string(x_83);
x_86 = lean_string_append(x_84, x_85);
lean_dec_ref(x_85);
x_87 = 2;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_box(0);
x_90 = lean_array_push(x_73, x_88);
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_90);
x_91 = x_81;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_76);
lean_ctor_set(x_94, 2, x_77);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_94, sizeof(void*)*3 + 1, x_75);
x_91 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_92; 
x_92 = l_Lake_getArtifacts_x3f___redArg___lam__1(x_72, x_89, x_54, x_55, x_56, x_57, x_58, x_91);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_32 = x_92;
goto block_47;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_64);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_100 = lean_ctor_get(x_66, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_66, 1);
lean_inc(x_101);
lean_dec_ref(x_66);
x_16 = x_100;
x_17 = x_101;
goto block_31;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_12 = x_59;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = x_59;
goto block_15;
}
}
block_115:
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = 2;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_push(x_108, x_112);
x_114 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_105);
lean_ctor_set_uint8(x_114, sizeof(void*)*3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*3 + 1, x_107);
x_52 = x_104;
x_53 = x_106;
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_114;
goto block_102;
}
block_208:
{
lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_207; 
x_121 = lean_ctor_get(x_120, 0);
x_122 = lean_ctor_get_uint8(x_120, sizeof(void*)*3);
x_123 = lean_ctor_get_uint8(x_120, sizeof(void*)*3 + 1);
x_124 = lean_ctor_get(x_120, 1);
x_125 = lean_ctor_get(x_120, 2);
x_207 = !lean_is_exclusive(x_120);
if (x_207 == 0)
{
x_126 = x_120;
x_127 = x_207;
goto block_206;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_121);
lean_dec(x_120);
x_126 = lean_box(0);
x_127 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lake_Package_cacheScope(x_4);
lean_inc_ref(x_128);
lean_inc_ref(x_51);
x_129 = l_Lake_Cache_readOutputs_x3f(x_51, x_128, x_2, x_121);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
if (x_127 == 0)
{
lean_ctor_set(x_126, 0, x_131);
x_132 = x_126;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_193, 0, x_131);
lean_ctor_set(x_193, 1, x_124);
lean_ctor_set(x_193, 2, x_125);
lean_ctor_set_uint8(x_193, sizeof(void*)*3, x_122);
lean_ctor_set_uint8(x_193, sizeof(void*)*3 + 1, x_123);
x_132 = x_193;
goto block_192;
}
block_192:
{
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_191; 
x_133 = lean_ctor_get(x_130, 0);
x_191 = !lean_is_exclusive(x_130);
if (x_191 == 0)
{
x_134 = x_130;
x_135 = x_191;
goto block_190;
}
else
{
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_box(0);
x_135 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_189; 
x_136 = lean_ctor_get(x_133, 0);
x_137 = lean_ctor_get(x_133, 1);
x_138 = lean_ctor_get(x_133, 2);
x_189 = !lean_is_exclusive(x_133);
if (x_189 == 0)
{
x_139 = x_133;
x_140 = x_189;
goto block_188;
}
else
{
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_133);
x_139 = lean_box(0);
x_140 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_141; 
lean_inc_ref(x_1);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_141 = lean_apply_10(x_1, x_136, x_137, x_138, x_5, x_6, x_7, x_8, x_9, x_132, lean_box(0));
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_153; 
lean_del_object(x_139);
lean_dec_ref(x_128);
lean_dec_ref(x_51);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_142 = lean_ctor_get(x_141, 0);
x_143 = lean_ctor_get(x_141, 1);
x_153 = !lean_is_exclusive(x_141);
if (x_153 == 0)
{
x_144 = x_141;
x_145 = x_153;
goto block_152;
}
else
{
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_146; 
if (x_135 == 0)
{
lean_ctor_set(x_134, 0, x_142);
x_146 = x_134;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_142);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_146);
x_147 = x_144;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_143);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_del_object(x_134);
x_154 = lean_ctor_get(x_141, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_141, 0);
lean_inc(x_155);
lean_dec_ref(x_141);
x_156 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get_uint8(x_154, sizeof(void*)*3);
x_158 = lean_ctor_get_uint8(x_154, sizeof(void*)*3 + 1);
x_159 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_154, 2);
lean_inc(x_160);
lean_dec(x_154);
x_161 = lean_array_get_size(x_156);
lean_inc(x_155);
x_162 = l_Array_extract___redArg(x_156, x_155, x_161);
x_163 = l_Array_shrink___redArg(x_156, x_155);
lean_dec(x_155);
x_164 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__2));
x_165 = l_Lake_Hash_hex(x_2);
x_166 = lean_unsigned_to_nat(7u);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_string_utf8_byte_size(x_165);
lean_inc_ref(x_165);
if (x_140 == 0)
{
lean_ctor_set(x_139, 2, x_168);
lean_ctor_set(x_139, 1, x_167);
lean_ctor_set(x_139, 0, x_165);
x_169 = x_139;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_187, 0, x_165);
lean_ctor_set(x_187, 1, x_167);
lean_ctor_set(x_187, 2, x_168);
x_169 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_170 = l_String_Slice_Pos_nextn(x_169, x_167, x_166);
lean_dec_ref(x_169);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_170);
x_172 = l_String_Slice_toString(x_171);
lean_dec_ref(x_171);
x_173 = lean_string_append(x_164, x_172);
lean_dec_ref(x_172);
x_174 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__3));
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_array_get_size(x_162);
x_177 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
x_178 = lean_nat_dec_lt(x_167, x_176);
if (x_178 == 0)
{
lean_dec_ref(x_162);
x_103 = x_159;
x_104 = x_119;
x_105 = x_160;
x_106 = x_128;
x_107 = x_158;
x_108 = x_163;
x_109 = x_157;
x_110 = x_175;
goto block_115;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_176, x_176);
if (x_179 == 0)
{
if (x_178 == 0)
{
lean_dec_ref(x_162);
x_103 = x_159;
x_104 = x_119;
x_105 = x_160;
x_106 = x_128;
x_107 = x_158;
x_108 = x_163;
x_109 = x_157;
x_110 = x_175;
goto block_115;
}
else
{
size_t x_180; size_t x_181; lean_object* x_182; 
x_180 = 0;
x_181 = lean_usize_of_nat(x_176);
x_182 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_177, x_118, x_162, x_180, x_181, x_175);
x_103 = x_159;
x_104 = x_119;
x_105 = x_160;
x_106 = x_128;
x_107 = x_158;
x_108 = x_163;
x_109 = x_157;
x_110 = x_182;
goto block_115;
}
}
else
{
size_t x_183; size_t x_184; lean_object* x_185; 
x_183 = 0;
x_184 = lean_usize_of_nat(x_176);
x_185 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_177, x_118, x_162, x_183, x_184, x_175);
x_103 = x_159;
x_104 = x_119;
x_105 = x_160;
x_106 = x_128;
x_107 = x_158;
x_108 = x_163;
x_109 = x_157;
x_110 = x_185;
goto block_115;
}
}
}
}
}
}
}
else
{
lean_dec(x_130);
x_52 = x_119;
x_53 = x_128;
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_132;
goto block_102;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_205; 
lean_dec_ref(x_128);
lean_dec_ref(x_51);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_129, 0);
x_195 = lean_ctor_get(x_129, 1);
x_205 = !lean_is_exclusive(x_129);
if (x_205 == 0)
{
x_196 = x_129;
x_197 = x_205;
goto block_204;
}
else
{
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_129);
x_196 = lean_box(0);
x_197 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_198; 
if (x_127 == 0)
{
lean_ctor_set(x_126, 0, x_195);
x_198 = x_126;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_203, 0, x_195);
lean_ctor_set(x_203, 1, x_124);
lean_ctor_set(x_203, 2, x_125);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_122);
lean_ctor_set_uint8(x_203, sizeof(void*)*3 + 1, x_123);
x_198 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_199; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 1, x_198);
x_199 = x_196;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_198);
x_199 = x_201;
goto block_200;
}
block_200:
{
return x_199;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_13 = l_Lake_getArtifacts_x3f___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_getArtifacts_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_14 = l_Lake_getArtifacts_x3f(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec_ref(x_5);
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_ctor_get(x_35, 2);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_35, 3);
lean_inc_ref(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_44 = lean_ctor_get(x_1, 0);
x_45 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
x_46 = l_System_FilePath_join(x_42, x_45);
x_145 = lean_string_utf8_byte_size(x_44);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = l_Lake_Hash_hex(x_43);
x_149 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_string_append(x_150, x_44);
x_47 = x_151;
goto block_144;
}
else
{
lean_object* x_152; 
x_152 = l_Lake_Hash_hex(x_43);
x_47 = x_152;
goto block_144;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_34:
{
lean_object* x_20; 
x_20 = lean_io_metadata(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_17);
x_8 = x_14;
x_9 = x_22;
x_10 = x_23;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec_ref(x_20);
x_25 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__0));
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_15);
x_31 = lean_array_push(x_15, x_29);
x_32 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_19);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 1, x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_144:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lake_joinRelative(x_46, x_47);
x_49 = lean_io_metadata(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_41);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_51);
lean_dec(x_50);
x_8 = x_48;
x_9 = x_51;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_140; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_36);
x_140 = !lean_is_exclusive(x_6);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_6, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_6, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_6, 0);
lean_dec(x_143);
x_52 = x_6;
x_53 = x_140;
goto block_139;
}
else
{
lean_dec(x_6);
x_52 = lean_box(0);
x_53 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec_ref(x_49);
if (lean_obj_tag(x_54) == 11)
{
lean_dec_ref(x_54);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_dec_ref(x_41);
x_57 = lean_box(0);
lean_inc(x_55);
x_58 = l_Lean_Name_str___override(x_57, x_55);
x_59 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_56, x_58);
lean_dec(x_58);
lean_dec(x_56);
if (lean_obj_tag(x_59) == 1)
{
lean_dec(x_55);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec_ref(x_3);
x_62 = l_Lake_CacheService_artifactUrl(x_43, x_60, x_61);
x_63 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__1));
x_64 = l_Lake_Hash_hex(x_43);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__2));
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_48);
x_69 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__3));
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_62);
x_72 = 0;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_push(x_36, x_73);
lean_inc_ref(x_48);
x_75 = l_Lake_downloadArtifactCore(x_43, x_62, x_48, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_del_object(x_52);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = 1;
x_78 = 0;
x_79 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, 2, x_4);
lean_inc_ref_n(x_79, 2);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_IO_setAccessRights(x_48, x_80);
lean_dec_ref(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_14 = x_48;
x_15 = x_76;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_40;
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__4));
x_84 = lean_io_error_to_string(x_82);
x_85 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_86 = 2;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_76, x_87);
x_14 = x_48;
x_15 = x_88;
x_16 = x_37;
x_17 = x_38;
x_18 = x_39;
x_19 = x_40;
goto block_34;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_100; 
lean_dec_ref(x_48);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
x_100 = !lean_is_exclusive(x_75);
if (x_100 == 0)
{
x_91 = x_75;
x_92 = x_100;
goto block_99;
}
else
{
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
x_91 = lean_box(0);
x_92 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_93; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_90);
x_93 = x_52;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_39);
lean_ctor_set(x_98, 2, x_40);
lean_ctor_set_uint8(x_98, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_98, sizeof(void*)*3 + 1, x_38);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_92 == 0)
{
lean_ctor_set(x_91, 1, x_93);
x_94 = x_91;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_93);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_59);
lean_dec_ref(x_48);
lean_dec(x_3);
lean_dec_ref(x_1);
x_101 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__6));
x_102 = lean_array_get_size(x_36);
x_103 = lean_array_push(x_36, x_101);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_103);
x_104 = x_52;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_39);
lean_ctor_set(x_107, 2, x_40);
lean_ctor_set_uint8(x_107, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_107, sizeof(void*)*3 + 1, x_38);
x_104 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_59);
lean_dec_ref(x_48);
lean_dec(x_3);
lean_dec_ref(x_1);
x_108 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__7));
x_109 = lean_string_append(x_108, x_55);
lean_dec(x_55);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_36);
x_113 = lean_array_push(x_36, x_111);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_113);
x_114 = x_52;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_39);
lean_ctor_set(x_117, 2, x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_117, sizeof(void*)*3 + 1, x_38);
x_114 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_41);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__8));
x_119 = lean_string_append(x_118, x_48);
lean_dec_ref(x_48);
x_120 = 3;
x_121 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_120);
x_122 = lean_array_get_size(x_36);
x_123 = lean_array_push(x_36, x_121);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_123);
x_124 = x_52;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_39);
lean_ctor_set(x_127, 2, x_40);
lean_ctor_set_uint8(x_127, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_127, sizeof(void*)*3 + 1, x_38);
x_124 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_48);
lean_dec_ref(x_41);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__9));
x_129 = lean_io_error_to_string(x_54);
x_130 = lean_string_append(x_128, x_129);
lean_dec_ref(x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_get_size(x_36);
x_134 = lean_array_push(x_36, x_132);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_134);
x_135 = x_52;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_39);
lean_ctor_set(x_138, 2, x_40);
lean_ctor_set_uint8(x_138, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_138, sizeof(void*)*3 + 1, x_38);
x_135 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_Lake_resolveArtifact___redArg(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_resolveArtifact___redArg(x_1, x_2, x_3, x_4, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_resolveArtifact(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lake_ArtifactDescr_fromJson_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_36; 
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
x_15 = x_6;
x_16 = x_36;
goto block_35;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0));
x_18 = l_Lean_Json_render(x_1);
x_19 = lean_unsigned_to_nat(80u);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Std_Format_pretty(x_18, x_19, x_20, x_21);
x_23 = lean_string_append(x_17, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1));
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_9);
lean_dec(x_9);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_10);
x_30 = lean_array_push(x_10, x_28);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_30);
x_31 = x_15;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_13);
lean_ctor_set(x_34, 2, x_14);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_12);
x_31 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec_ref(x_8);
x_38 = l_Lake_resolveArtifact___redArg(x_37, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(x_1, x_2, x_3, x_4, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(x_2, x_3, x_4, x_1, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 11, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_26; 
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
x_10 = x_7;
x_11 = x_26;
goto block_25;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_21; 
x_21 = lean_io_metadata(x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_23);
lean_dec(x_22);
x_12 = x_9;
x_13 = x_23;
goto block_20;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_21);
x_24 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_12 = x_9;
x_13 = x_24;
goto block_20;
}
block_20:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_12);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
x_29 = x_7;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lake_computeArtifact___redArg(x_1, x_2, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_computeArtifact___redArg(x_1, x_2, x_3, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_computeArtifact(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_20; 
x_20 = l_System_FilePath_pathExists(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_39 = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
x_40 = lean_string_append(x_39, x_22);
x_41 = 0;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_4, x_42);
lean_inc_ref(x_1);
x_44 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
x_45 = lean_io_hard_link(x_22, x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_23 = x_43;
goto block_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
x_48 = lean_io_error_to_string(x_46);
x_49 = lean_string_append(x_47, x_48);
lean_dec_ref(x_48);
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_41);
x_51 = lean_array_push(x_43, x_50);
x_52 = l_Lake_copyFile(x_22, x_1);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_52);
x_53 = 1;
x_54 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, 1, x_20);
lean_ctor_set_uint8(x_54, 2, x_3);
lean_inc_ref_n(x_54, 2);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_IO_setAccessRights(x_1, x_55);
lean_dec_ref(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_dec_ref(x_56);
x_23 = x_51;
goto block_38;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_io_error_to_string(x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_51);
x_62 = lean_array_push(x_51, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_dec_ref(x_52);
x_65 = lean_io_error_to_string(x_64);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_get_size(x_51);
x_69 = lean_array_push(x_51, x_67);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_44, 0);
lean_inc(x_71);
lean_dec_ref(x_44);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_43);
x_76 = lean_array_push(x_43, x_74);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
block_38:
{
uint64_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_25 = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
x_26 = lean_string_append(x_25, x_1);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_push(x_23, x_28);
lean_inc_ref(x_1);
x_30 = l_Lake_writeFileHash(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
x_6 = x_29;
goto block_19;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_29);
x_36 = lean_array_push(x_29, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
x_6 = x_4;
goto block_19;
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 3);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_9 = x_2;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; 
lean_inc_ref(x_1);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 1, x_1);
x_11 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_8);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_restoreArtifact(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_5 = lean_io_mono_ms_now();
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_11 = x_3;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_15);
x_16 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_8);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_215; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get(x_14, 1);
x_36 = lean_ctor_get(x_14, 2);
x_215 = !lean_is_exclusive(x_14);
if (x_215 == 0)
{
x_37 = x_14;
x_38 = x_215;
goto block_214;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_32);
lean_dec(x_14);
x_37 = lean_box(0);
x_38 = x_215;
goto block_214;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
x_26 = lean_array_get_size(x_20);
x_27 = lean_array_push(x_20, x_25);
x_28 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
block_214:
{
uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get_uint8(x_31, sizeof(void*)*2 + 2);
x_40 = l_Lake_JobAction_merge(x_33, x_9);
x_41 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(x_8);
x_42 = l_System_FilePath_addExtension(x_8, x_41);
if (x_39 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; 
x_43 = lean_io_mono_ms_now();
x_50 = l_Lake_removeFileIfExists(x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
lean_inc_ref(x_32);
if (x_38 == 0)
{
x_51 = x_37;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_189, 0, x_32);
lean_ctor_set(x_189, 1, x_35);
lean_ctor_set(x_189, 2, x_36);
lean_ctor_set_uint8(x_189, sizeof(void*)*3 + 1, x_34);
x_51 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_52; 
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_40);
lean_inc_ref(x_13);
x_52 = lean_apply_7(x_2, x_6, x_10, x_11, x_12, x_13, x_51, lean_box(0));
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 0);
x_55 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
x_56 = lean_ctor_get_uint8(x_53, sizeof(void*)*3 + 1);
x_57 = lean_ctor_get(x_53, 1);
x_58 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_1);
x_59 = l_Lake_clearFileHash(x_1);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec_ref(x_59);
x_60 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; uint8_t x_152; 
x_152 = !lean_is_exclusive(x_60);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_60, 0);
lean_dec(x_153);
x_61 = x_60;
x_62 = x_152;
goto block_151;
}
else
{
lean_dec(x_60);
x_61 = lean_box(0);
x_62 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_63; 
x_63 = l_Lake_computeArtifact___redArg(x_1, x_4, x_5, x_13, x_53);
lean_dec_ref(x_13);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_ctor_get(x_65, 0);
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get_uint8(x_64, sizeof(void*)*3);
x_69 = lean_ctor_get_uint8(x_64, sizeof(void*)*3 + 1);
x_70 = lean_ctor_get(x_64, 1);
x_71 = lean_ctor_get(x_64, 2);
x_72 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_73 = lean_ctor_get(x_66, 0);
x_74 = lean_array_get_size(x_32);
lean_dec_ref(x_32);
x_75 = lean_array_get_size(x_67);
x_76 = l_Array_extract___redArg(x_67, x_74, x_75);
x_141 = lean_string_utf8_byte_size(x_73);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_nat_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = l_Lake_Hash_hex(x_72);
x_145 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_string_append(x_146, x_73);
x_77 = x_147;
goto block_140;
}
else
{
lean_object* x_148; 
x_148 = l_Lake_Hash_hex(x_72);
x_77 = x_148;
goto block_140;
}
block_140:
{
lean_object* x_78; 
if (x_62 == 0)
{
lean_ctor_set_tag(x_61, 3);
lean_ctor_set(x_61, 0, x_77);
x_78 = x_61;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_77);
x_78 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_79; lean_object* x_80; 
x_79 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_78, x_76);
x_80 = l_Lake_BuildMetadata_writeFile(x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; uint8_t x_121; 
x_121 = !lean_is_exclusive(x_80);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_80, 0);
lean_dec(x_122);
x_81 = x_80;
x_82 = x_121;
goto block_120;
}
else
{
lean_dec(x_80);
x_81 = lean_box(0);
x_82 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_83; 
x_83 = l_Lake_removeFileIfExists(x_42);
lean_dec_ref(x_42);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; uint8_t x_103; 
x_103 = !lean_is_exclusive(x_83);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_83, 0);
lean_dec(x_104);
x_84 = x_83;
x_85 = x_103;
goto block_102;
}
else
{
lean_dec(x_83);
x_84 = lean_box(0);
x_85 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_86; 
lean_inc(x_65);
if (x_85 == 0)
{
lean_ctor_set(x_84, 0, x_65);
x_86 = x_84;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_65);
x_86 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_87; 
if (x_82 == 0)
{
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 0, x_86);
x_87 = x_81;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_86);
x_87 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
x_88 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_43, x_87, x_64);
lean_dec_ref(x_87);
lean_dec(x_43);
x_89 = lean_ctor_get(x_88, 1);
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_90 = x_88;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
lean_ctor_set(x_90, 0, x_65);
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_65);
lean_ctor_set(x_94, 1, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_116; 
lean_inc(x_71);
lean_inc_ref(x_70);
lean_inc_ref(x_67);
lean_del_object(x_81);
lean_dec(x_65);
x_116 = !lean_is_exclusive(x_64);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_64, 2);
lean_dec(x_117);
x_118 = lean_ctor_get(x_64, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_64, 0);
lean_dec(x_119);
x_105 = x_64;
x_106 = x_116;
goto block_115;
}
else
{
lean_dec(x_64);
x_105 = lean_box(0);
x_106 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_83, 0);
lean_inc(x_107);
lean_dec_ref(x_83);
x_108 = lean_io_error_to_string(x_107);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_67, x_110);
if (x_106 == 0)
{
lean_ctor_set(x_105, 0, x_111);
x_112 = x_105;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_70);
lean_ctor_set(x_114, 2, x_71);
lean_ctor_set_uint8(x_114, sizeof(void*)*3, x_68);
lean_ctor_set_uint8(x_114, sizeof(void*)*3 + 1, x_69);
x_112 = x_114;
goto block_113;
}
block_113:
{
x_44 = x_75;
x_45 = x_112;
goto block_49;
}
}
}
}
}
else
{
lean_object* x_123; uint8_t x_124; uint8_t x_134; 
lean_inc(x_71);
lean_inc_ref(x_70);
lean_inc_ref(x_67);
lean_dec(x_65);
lean_dec_ref(x_42);
x_134 = !lean_is_exclusive(x_64);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_64, 2);
lean_dec(x_135);
x_136 = lean_ctor_get(x_64, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_64, 0);
lean_dec(x_137);
x_123 = x_64;
x_124 = x_134;
goto block_133;
}
else
{
lean_dec(x_64);
x_123 = lean_box(0);
x_124 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_80, 0);
lean_inc(x_125);
lean_dec_ref(x_80);
x_126 = lean_io_error_to_string(x_125);
x_127 = 3;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = lean_array_push(x_67, x_128);
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_129);
x_130 = x_123;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_70);
lean_ctor_set(x_132, 2, x_71);
lean_ctor_set_uint8(x_132, sizeof(void*)*3, x_68);
lean_ctor_set_uint8(x_132, sizeof(void*)*3 + 1, x_69);
x_130 = x_132;
goto block_131;
}
block_131:
{
x_44 = x_75;
x_45 = x_130;
goto block_49;
}
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_del_object(x_61);
lean_dec_ref(x_42);
lean_dec_ref(x_32);
lean_dec_ref(x_8);
x_149 = lean_ctor_get(x_63, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_63, 1);
lean_inc(x_150);
lean_dec_ref(x_63);
x_44 = x_149;
x_45 = x_150;
goto block_49;
}
}
}
else
{
lean_object* x_154; uint8_t x_155; uint8_t x_166; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc_ref(x_54);
lean_dec_ref(x_42);
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_166 = !lean_is_exclusive(x_53);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_53, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_53, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_53, 0);
lean_dec(x_169);
x_154 = x_53;
x_155 = x_166;
goto block_165;
}
else
{
lean_dec(x_53);
x_154 = lean_box(0);
x_155 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_60, 0);
lean_inc(x_156);
lean_dec_ref(x_60);
x_157 = lean_io_error_to_string(x_156);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_get_size(x_54);
x_161 = lean_array_push(x_54, x_159);
if (x_155 == 0)
{
lean_ctor_set(x_154, 0, x_161);
x_162 = x_154;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_57);
lean_ctor_set(x_164, 2, x_58);
lean_ctor_set_uint8(x_164, sizeof(void*)*3, x_55);
lean_ctor_set_uint8(x_164, sizeof(void*)*3 + 1, x_56);
x_162 = x_164;
goto block_163;
}
block_163:
{
x_44 = x_160;
x_45 = x_162;
goto block_49;
}
}
}
}
else
{
lean_object* x_170; uint8_t x_171; uint8_t x_182; 
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc_ref(x_54);
lean_dec_ref(x_42);
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_182 = !lean_is_exclusive(x_53);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_53, 2);
lean_dec(x_183);
x_184 = lean_ctor_get(x_53, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_53, 0);
lean_dec(x_185);
x_170 = x_53;
x_171 = x_182;
goto block_181;
}
else
{
lean_dec(x_53);
x_170 = lean_box(0);
x_171 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_59, 0);
lean_inc(x_172);
lean_dec_ref(x_59);
x_173 = lean_io_error_to_string(x_172);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_array_get_size(x_54);
x_177 = lean_array_push(x_54, x_175);
if (x_171 == 0)
{
lean_ctor_set(x_170, 0, x_177);
x_178 = x_170;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_57);
lean_ctor_set(x_180, 2, x_58);
lean_ctor_set_uint8(x_180, sizeof(void*)*3, x_55);
lean_ctor_set_uint8(x_180, sizeof(void*)*3 + 1, x_56);
x_178 = x_180;
goto block_179;
}
block_179:
{
x_44 = x_176;
x_45 = x_178;
goto block_49;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_42);
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_186 = lean_ctor_get(x_52, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_52, 1);
lean_inc(x_187);
lean_dec_ref(x_52);
x_44 = x_186;
x_45 = x_187;
goto block_49;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec_ref(x_42);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_190 = lean_ctor_get(x_50, 0);
lean_inc(x_190);
lean_dec_ref(x_50);
x_191 = lean_io_error_to_string(x_190);
x_192 = 3;
x_193 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_192);
x_194 = lean_array_get_size(x_32);
x_195 = lean_array_push(x_32, x_193);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_195);
x_196 = x_37;
goto block_197;
}
else
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_35);
lean_ctor_set(x_198, 2, x_36);
lean_ctor_set_uint8(x_198, sizeof(void*)*3 + 1, x_34);
x_196 = x_198;
goto block_197;
}
block_197:
{
lean_ctor_set_uint8(x_196, sizeof(void*)*3, x_40);
x_44 = x_194;
x_45 = x_196;
goto block_49;
}
}
block_49:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_box(0);
x_47 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_43, x_46, x_45);
lean_dec(x_43);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_16 = x_44;
x_17 = x_48;
goto block_19;
}
}
else
{
uint8_t x_199; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_199 = l_System_FilePath_pathExists(x_8);
lean_dec_ref(x_8);
if (x_199 == 0)
{
lean_dec_ref(x_42);
lean_del_object(x_37);
x_20 = x_32;
x_21 = x_40;
x_22 = x_39;
x_23 = x_35;
x_24 = x_36;
goto block_30;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_box(0);
x_201 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
x_202 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_200, x_201);
x_203 = l_Lake_BuildMetadata_writeFile(x_42, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_dec_ref(x_203);
lean_del_object(x_37);
x_20 = x_32;
x_21 = x_40;
x_22 = x_39;
x_23 = x_35;
x_24 = x_36;
goto block_30;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_io_error_to_string(x_204);
x_206 = 3;
x_207 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_206);
x_208 = lean_array_get_size(x_32);
x_209 = lean_array_push(x_32, x_207);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_209);
x_210 = x_37;
goto block_212;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_35);
lean_ctor_set(x_213, 2, x_36);
x_210 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_211; 
lean_ctor_set_uint8(x_210, sizeof(void*)*3, x_40);
lean_ctor_set_uint8(x_210, sizeof(void*)*3 + 1, x_39);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_9);
x_18 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 3;
lean_inc_ref(x_6);
x_15 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_6, x_4, x_3, x_7, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_io_metadata(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 3);
lean_dec(x_24);
x_16 = x_1;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 3, x_12);
x_18 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_12);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec_ref(x_10);
if (lean_obj_tag(x_25) == 11)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_41; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_3, 0);
lean_dec(x_44);
x_27 = x_3;
x_28 = x_41;
goto block_40;
}
else
{
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
x_30 = lean_io_error_to_string(x_25);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_5);
x_35 = lean_array_push(x_5, x_33);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_35);
x_36 = x_27;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_8);
lean_ctor_set(x_39, 2, x_9);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_7);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(x_1, x_2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
x_8 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0));
x_9 = lean_string_append(x_4, x_8);
x_10 = lean_string_append(x_9, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_32; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_116; lean_object* x_117; lean_object* x_205; lean_object* x_206; 
x_48 = lean_ctor_get(x_9, 1);
x_49 = lean_ctor_get(x_48, 0);
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_ctor_get(x_48, 3);
lean_inc_ref(x_51);
x_205 = lean_ctor_get(x_5, 6);
x_206 = lean_ctor_get(x_205, 25);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_50, 6);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_49, 6);
x_209 = lean_ctor_get(x_208, 25);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = 0;
x_116 = x_210;
x_117 = x_10;
goto block_204;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_unbox(x_211);
x_116 = x_212;
x_117 = x_10;
goto block_204;
}
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_207, 0);
x_214 = lean_unbox(x_213);
x_116 = x_214;
x_117 = x_10;
goto block_204;
}
}
else
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_206, 0);
x_216 = lean_unbox(x_215);
x_116 = x_216;
x_117 = x_10;
goto block_204;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_31:
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
x_23 = x_17;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_18);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Array_shrink___redArg(x_18, x_16);
lean_dec(x_16);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_20);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_12 = x_26;
goto block_15;
}
}
}
block_47:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_32, 0);
lean_dec(x_43);
x_35 = x_32;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec_ref(x_33);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_34);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec_ref(x_32);
x_12 = x_44;
goto block_15;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_dec_ref(x_32);
x_16 = x_45;
x_17 = x_46;
goto block_31;
}
}
block_102:
{
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_60; uint64_t x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_4);
x_61 = lean_ctor_get_uint64(x_60, sizeof(void*)*3);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_uint64_dec_eq(x_61, x_3);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_12 = x_59;
goto block_15;
}
else
{
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_box(0);
lean_inc_ref(x_58);
lean_inc(x_64);
x_66 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(x_64, x_65, x_65, x_1, x_58, x_59);
if (lean_obj_tag(x_66) == 0)
{
if (x_52 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_box(0);
x_70 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(x_67, x_69, x_54, x_55, x_56, x_57, x_58, x_68);
lean_dec_ref(x_58);
x_32 = x_70;
goto block_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec_ref(x_66);
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
x_75 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 1);
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_71, 2);
x_78 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_51, x_53, x_3, x_64, x_65, x_65);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_78);
x_79 = lean_box(0);
x_80 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(x_72, x_79, x_54, x_55, x_56, x_57, x_58, x_71);
lean_dec_ref(x_58);
x_32 = x_80;
goto block_47;
}
else
{
lean_object* x_81; uint8_t x_82; uint8_t x_96; 
lean_inc(x_77);
lean_inc_ref(x_76);
lean_inc_ref(x_73);
x_96 = !lean_is_exclusive(x_71);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_71, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_71, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_71, 0);
lean_dec(x_99);
x_81 = x_71;
x_82 = x_96;
goto block_95;
}
else
{
lean_dec(x_71);
x_81 = lean_box(0);
x_82 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec_ref(x_78);
x_84 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_85 = lean_io_error_to_string(x_83);
x_86 = lean_string_append(x_84, x_85);
lean_dec_ref(x_85);
x_87 = 2;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_box(0);
x_90 = lean_array_push(x_73, x_88);
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_90);
x_91 = x_81;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_76);
lean_ctor_set(x_94, 2, x_77);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_94, sizeof(void*)*3 + 1, x_75);
x_91 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_92; 
x_92 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(x_72, x_89, x_54, x_55, x_56, x_57, x_58, x_91);
lean_dec_ref(x_58);
x_32 = x_92;
goto block_47;
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_64);
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_100 = lean_ctor_get(x_66, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_66, 1);
lean_inc(x_101);
lean_dec_ref(x_66);
x_16 = x_100;
x_17 = x_101;
goto block_31;
}
}
else
{
lean_dec(x_62);
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_12 = x_59;
goto block_15;
}
}
}
else
{
lean_dec_ref(x_58);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
lean_dec(x_4);
x_12 = x_59;
goto block_15;
}
}
block_115:
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = 2;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_push(x_105, x_112);
x_114 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set_uint8(x_114, sizeof(void*)*3, x_107);
lean_ctor_set_uint8(x_114, sizeof(void*)*3 + 1, x_109);
x_52 = x_103;
x_53 = x_104;
x_54 = x_2;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_114;
goto block_102;
}
block_204:
{
lean_object* x_118; uint8_t x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_203; 
x_118 = lean_ctor_get(x_117, 0);
x_119 = lean_ctor_get_uint8(x_117, sizeof(void*)*3);
x_120 = lean_ctor_get_uint8(x_117, sizeof(void*)*3 + 1);
x_121 = lean_ctor_get(x_117, 1);
x_122 = lean_ctor_get(x_117, 2);
x_203 = !lean_is_exclusive(x_117);
if (x_203 == 0)
{
x_123 = x_117;
x_124 = x_203;
goto block_202;
}
else
{
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_118);
lean_dec(x_117);
x_123 = lean_box(0);
x_124 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_125);
lean_inc_ref(x_51);
x_126 = l_Lake_Cache_readOutputs_x3f(x_51, x_125, x_3, x_118);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_128);
x_129 = x_123;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_189, 0, x_128);
lean_ctor_set(x_189, 1, x_121);
lean_ctor_set(x_189, 2, x_122);
lean_ctor_set_uint8(x_189, sizeof(void*)*3, x_119);
lean_ctor_set_uint8(x_189, sizeof(void*)*3 + 1, x_120);
x_129 = x_189;
goto block_188;
}
block_188:
{
if (lean_obj_tag(x_127) == 1)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_187; 
x_130 = lean_ctor_get(x_127, 0);
x_187 = !lean_is_exclusive(x_127);
if (x_187 == 0)
{
x_131 = x_127;
x_132 = x_187;
goto block_186;
}
else
{
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_box(0);
x_132 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_185; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = lean_ctor_get(x_130, 1);
x_135 = lean_ctor_get(x_130, 2);
x_185 = !lean_is_exclusive(x_130);
if (x_185 == 0)
{
x_136 = x_130;
x_137 = x_185;
goto block_184;
}
else
{
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_130);
x_136 = lean_box(0);
x_137 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_138; 
lean_inc_ref(x_9);
x_138 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(x_133, x_134, x_135, x_1, x_9, x_129);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_150; 
lean_del_object(x_136);
lean_dec_ref(x_125);
lean_dec_ref(x_51);
lean_dec_ref(x_9);
lean_dec(x_4);
x_139 = lean_ctor_get(x_138, 0);
x_140 = lean_ctor_get(x_138, 1);
x_150 = !lean_is_exclusive(x_138);
if (x_150 == 0)
{
x_141 = x_138;
x_142 = x_150;
goto block_149;
}
else
{
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_138);
x_141 = lean_box(0);
x_142 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_143; 
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_139);
x_143 = x_131;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_139);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_142 == 0)
{
lean_ctor_set(x_141, 0, x_143);
x_144 = x_141;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_140);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_del_object(x_131);
x_151 = lean_ctor_get(x_138, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_138, 0);
lean_inc(x_152);
lean_dec_ref(x_138);
x_153 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_153);
x_154 = lean_ctor_get_uint8(x_151, sizeof(void*)*3);
x_155 = lean_ctor_get_uint8(x_151, sizeof(void*)*3 + 1);
x_156 = lean_ctor_get(x_151, 1);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_151, 2);
lean_inc(x_157);
lean_dec(x_151);
x_158 = lean_array_get_size(x_153);
lean_inc(x_152);
x_159 = l_Array_extract___redArg(x_153, x_152, x_158);
x_160 = l_Array_shrink___redArg(x_153, x_152);
lean_dec(x_152);
x_161 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__2));
x_162 = l_Lake_Hash_hex(x_3);
x_163 = lean_unsigned_to_nat(7u);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_string_utf8_byte_size(x_162);
lean_inc_ref(x_162);
if (x_137 == 0)
{
lean_ctor_set(x_136, 2, x_165);
lean_ctor_set(x_136, 1, x_164);
lean_ctor_set(x_136, 0, x_162);
x_166 = x_136;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_162);
lean_ctor_set(x_183, 1, x_164);
lean_ctor_set(x_183, 2, x_165);
x_166 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_167 = l_String_Slice_Pos_nextn(x_166, x_164, x_163);
lean_dec_ref(x_166);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_String_Slice_toString(x_168);
lean_dec_ref(x_168);
x_170 = lean_string_append(x_161, x_169);
lean_dec_ref(x_169);
x_171 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__3));
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_array_get_size(x_159);
x_174 = lean_nat_dec_lt(x_164, x_173);
if (x_174 == 0)
{
lean_dec_ref(x_159);
x_103 = x_116;
x_104 = x_125;
x_105 = x_160;
x_106 = x_156;
x_107 = x_154;
x_108 = x_157;
x_109 = x_155;
x_110 = x_172;
goto block_115;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_173, x_173);
if (x_175 == 0)
{
if (x_174 == 0)
{
lean_dec_ref(x_159);
x_103 = x_116;
x_104 = x_125;
x_105 = x_160;
x_106 = x_156;
x_107 = x_154;
x_108 = x_157;
x_109 = x_155;
x_110 = x_172;
goto block_115;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; 
x_176 = 0;
x_177 = lean_usize_of_nat(x_173);
x_178 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(x_159, x_176, x_177, x_172);
lean_dec_ref(x_159);
x_103 = x_116;
x_104 = x_125;
x_105 = x_160;
x_106 = x_156;
x_107 = x_154;
x_108 = x_157;
x_109 = x_155;
x_110 = x_178;
goto block_115;
}
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_173);
x_181 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(x_159, x_179, x_180, x_172);
lean_dec_ref(x_159);
x_103 = x_116;
x_104 = x_125;
x_105 = x_160;
x_106 = x_156;
x_107 = x_154;
x_108 = x_157;
x_109 = x_155;
x_110 = x_181;
goto block_115;
}
}
}
}
}
}
}
else
{
lean_dec(x_127);
x_52 = x_116;
x_53 = x_125;
x_54 = x_2;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_129;
goto block_102;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_201; 
lean_dec_ref(x_125);
lean_dec_ref(x_51);
lean_dec_ref(x_9);
lean_dec(x_4);
x_190 = lean_ctor_get(x_126, 0);
x_191 = lean_ctor_get(x_126, 1);
x_201 = !lean_is_exclusive(x_126);
if (x_201 == 0)
{
x_192 = x_126;
x_193 = x_201;
goto block_200;
}
else
{
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_126);
x_192 = lean_box(0);
x_193 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_194; 
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_191);
x_194 = x_123;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_121);
lean_ctor_set(x_199, 2, x_122);
lean_ctor_set_uint8(x_199, sizeof(void*)*3, x_119);
lean_ctor_set_uint8(x_199, sizeof(void*)*3 + 1, x_120);
x_194 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_195; 
if (x_193 == 0)
{
lean_ctor_set(x_192, 1, x_194);
x_195 = x_192;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_194);
x_195 = x_197;
goto block_196;
}
block_196:
{
return x_195;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint64_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_14 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(x_12, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_3);
x_15 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_8, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_155; 
x_17 = lean_ctor_get(x_15, 1);
x_155 = !lean_is_exclusive(x_15);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_15, 0);
lean_dec(x_156);
x_18 = x_15;
x_19 = x_155;
goto block_154;
}
else
{
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_20; lean_object* x_21; lean_object* x_68; 
x_20 = lean_ctor_get(x_16, 0);
x_68 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_2, x_3, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_142; 
x_71 = lean_ctor_get(x_68, 1);
x_142 = !lean_is_exclusive(x_68);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_68, 0);
lean_dec(x_143);
x_72 = x_68;
x_73 = x_142;
goto block_141;
}
else
{
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
x_73 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
x_76 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 1);
x_77 = lean_ctor_get(x_71, 1);
x_78 = lean_ctor_get(x_71, 2);
x_79 = l_Lake_removeFileIfExists(x_5);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; uint8_t x_120; 
x_120 = !lean_is_exclusive(x_79);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_79, 0);
lean_dec(x_121);
x_80 = x_79;
x_81 = x_120;
goto block_119;
}
else
{
lean_dec(x_79);
x_80 = lean_box(0);
x_81 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_82; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_20, 0);
x_109 = lean_ctor_get_uint64(x_108, sizeof(void*)*1);
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_string_utf8_byte_size(x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_nat_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = l_Lake_Hash_hex(x_109);
x_115 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_110);
x_82 = x_117;
goto block_107;
}
else
{
lean_object* x_118; 
x_118 = l_Lake_Hash_hex(x_109);
x_82 = x_118;
goto block_107;
}
block_107:
{
lean_object* x_83; 
if (x_81 == 0)
{
lean_ctor_set_tag(x_80, 3);
lean_ctor_set(x_80, 0, x_82);
x_83 = x_80;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_82);
x_83 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lake_BuildMetadata_ofFetch(x_2, x_83);
x_85 = l_Lake_BuildMetadata_writeFile(x_6, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
lean_del_object(x_72);
x_21 = x_71;
goto block_67;
}
else
{
lean_object* x_86; uint8_t x_87; uint8_t x_101; 
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc_ref(x_74);
lean_del_object(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_5);
x_101 = !lean_is_exclusive(x_71);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_71, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_71, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_71, 0);
lean_dec(x_104);
x_86 = x_71;
x_87 = x_101;
goto block_100;
}
else
{
lean_dec(x_71);
x_86 = lean_box(0);
x_87 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec_ref(x_85);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_74);
x_93 = lean_array_push(x_74, x_91);
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_93);
x_94 = x_86;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_77);
lean_ctor_set(x_99, 2, x_78);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_75);
lean_ctor_set_uint8(x_99, sizeof(void*)*3 + 1, x_76);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_94);
lean_ctor_set(x_72, 0, x_92);
x_95 = x_72;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_94);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
}
}
}
else
{
lean_object* x_122; uint8_t x_123; uint8_t x_137; 
lean_inc(x_78);
lean_inc_ref(x_77);
lean_inc_ref(x_74);
lean_del_object(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_137 = !lean_is_exclusive(x_71);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_71, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_71, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_71, 0);
lean_dec(x_140);
x_122 = x_71;
x_123 = x_137;
goto block_136;
}
else
{
lean_dec(x_71);
x_122 = lean_box(0);
x_123 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_79, 0);
lean_inc(x_124);
lean_dec_ref(x_79);
x_125 = lean_io_error_to_string(x_124);
x_126 = 3;
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = lean_array_get_size(x_74);
x_129 = lean_array_push(x_74, x_127);
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_129);
x_130 = x_122;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_77);
lean_ctor_set(x_135, 2, x_78);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_75);
lean_ctor_set_uint8(x_135, sizeof(void*)*3 + 1, x_76);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_130);
lean_ctor_set(x_72, 0, x_128);
x_131 = x_72;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
else
{
lean_object* x_144; 
lean_dec_ref(x_6);
x_144 = lean_ctor_get(x_68, 1);
lean_inc(x_144);
lean_dec_ref(x_68);
x_21 = x_144;
goto block_67;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_del_object(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_145 = lean_ctor_get(x_68, 0);
x_146 = lean_ctor_get(x_68, 1);
x_153 = !lean_is_exclusive(x_68);
if (x_153 == 0)
{
x_147 = x_68;
x_148 = x_153;
goto block_152;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_68);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
block_67:
{
if (x_7 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_5);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_65; 
lean_inc(x_20);
lean_del_object(x_18);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_16, 0);
lean_dec(x_66);
x_25 = x_16;
x_26 = x_65;
goto block_64;
}
else
{
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_63; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_29 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 1);
x_30 = lean_ctor_get(x_21, 1);
x_31 = lean_ctor_get(x_21, 2);
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
x_32 = x_21;
x_33 = x_63;
goto block_62;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_27);
lean_dec(x_21);
x_32 = lean_box(0);
x_33 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_34; 
x_34 = l_Lake_restoreArtifact(x_5, x_20, x_1, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_49; 
x_35 = lean_ctor_get(x_34, 0);
x_36 = lean_ctor_get(x_34, 1);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
x_37 = x_34;
x_38 = x_49;
goto block_48;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_39; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_36);
x_39 = x_32;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_30);
lean_ctor_set(x_47, 2, x_31);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_28);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 1, x_29);
x_39 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_40; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_35);
x_40 = x_25;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_35);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_39);
lean_ctor_set(x_37, 0, x_40);
x_41 = x_37;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_39);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_61; 
lean_del_object(x_25);
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
x_52 = x_34;
x_53 = x_61;
goto block_60;
}
else
{
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_box(0);
x_53 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_54; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_51);
x_54 = x_32;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_30);
lean_ctor_set(x_59, 2, x_31);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_28);
lean_ctor_set_uint8(x_59, sizeof(void*)*3 + 1, x_29);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_54);
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_165; 
lean_dec(x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_157 = lean_ctor_get(x_15, 1);
x_165 = !lean_is_exclusive(x_15);
if (x_165 == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_15, 0);
lean_dec(x_166);
x_158 = x_15;
x_159 = x_165;
goto block_164;
}
else
{
lean_inc(x_157);
lean_dec(x_15);
x_158 = lean_box(0);
x_159 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_box(0);
if (x_159 == 0)
{
lean_ctor_set(x_158, 0, x_160);
x_161 = x_158;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_157);
x_161 = x_163;
goto block_162;
}
block_162:
{
return x_161;
}
}
}
}
else
{
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint64_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
x_16 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_17 = lean_unbox(x_7);
x_18 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_15, x_16, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, uint64_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; uint8_t x_18; 
x_17 = 1;
x_18 = l_Lake_instDecidableEqOutputStatus(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get(x_15, 1);
x_24 = lean_ctor_get(x_15, 2);
x_25 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_25);
lean_dec(x_19);
lean_inc_ref(x_25);
x_26 = l_Lake_Cache_saveArtifact(x_25, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_68; 
x_27 = lean_ctor_get(x_26, 0);
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
x_28 = x_26;
x_29 = x_68;
goto block_67;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lake_Package_cacheScope(x_7);
x_59 = lean_string_utf8_byte_size(x_32);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lake_Hash_hex(x_31);
x_63 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_32);
x_34 = x_65;
goto block_58;
}
else
{
lean_object* x_66; 
x_66 = l_Lake_Hash_hex(x_31);
x_34 = x_66;
goto block_58;
}
block_58:
{
lean_object* x_35; 
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 0, x_34);
x_35 = x_28;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_34);
x_35 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_25, x_33, x_8, x_35, x_36, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_15);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; uint8_t x_52; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_20);
lean_dec(x_27);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_15, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_15, 0);
lean_dec(x_55);
x_39 = x_15;
x_40 = x_52;
goto block_51;
}
else
{
lean_dec(x_15);
x_39 = lean_box(0);
x_40 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec_ref(x_37);
x_42 = lean_io_error_to_string(x_41);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_20);
x_46 = lean_array_push(x_20, x_44);
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_46);
x_47 = x_39;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_23);
lean_ctor_set(x_50, 2, x_24);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 1, x_22);
x_47 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_82; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_20);
lean_dec_ref(x_25);
lean_dec_ref(x_7);
x_82 = !lean_is_exclusive(x_15);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_15, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_15, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_15, 0);
lean_dec(x_85);
x_69 = x_15;
x_70 = x_82;
goto block_81;
}
else
{
lean_dec(x_15);
x_69 = lean_box(0);
x_70 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_26, 0);
lean_inc(x_71);
lean_dec_ref(x_26);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_20);
x_76 = lean_array_push(x_20, x_74);
if (x_70 == 0)
{
lean_ctor_set(x_69, 0, x_76);
x_77 = x_69;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_23);
lean_ctor_set(x_80, 2, x_24);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_80, sizeof(void*)*3 + 1, x_22);
x_77 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_86; 
lean_dec_ref(x_7);
x_86 = l_Lake_computeArtifact___redArg(x_2, x_3, x_4, x_14, x_15);
lean_dec_ref(x_14);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint64_t x_21; lean_object* x_22; 
x_17 = lean_unbox(x_1);
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = lean_unbox(x_6);
x_21 = lean_unbox_uint64(x_8);
lean_dec_ref(x_8);
x_22 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_17, x_2, x_3, x_18, x_19, x_20, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_261; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_261 = !lean_is_exclusive(x_12);
if (x_261 == 0)
{
x_19 = x_12;
x_20 = x_261;
goto block_260;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_51; 
x_21 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_22 = lean_string_append(x_1, x_21);
lean_inc_ref(x_22);
x_51 = l_Lake_readTraceFile(x_22, x_14);
if (lean_obj_tag(x_51) == 0)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_97; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_126; lean_object* x_156; uint8_t x_157; uint8_t x_196; uint8_t x_197; lean_object* x_198; uint8_t x_200; lean_object* x_201; lean_object* x_212; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_8, 0);
x_55 = lean_ctor_get_uint64(x_17, sizeof(void*)*3);
x_56 = lean_ctor_get(x_17, 2);
x_70 = lean_ctor_get(x_54, 6);
x_71 = lean_ctor_get(x_54, 23);
lean_inc(x_71);
x_101 = lean_ctor_get(x_70, 25);
x_102 = lean_ctor_get(x_70, 26);
lean_inc_ref(x_17);
x_212 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_212, 0, x_53);
lean_ctor_set(x_212, 1, x_17);
lean_ctor_set(x_212, 2, x_18);
lean_ctor_set_uint8(x_212, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_212, sizeof(void*)*3 + 1, x_16);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_11, 1);
x_214 = lean_ctor_get(x_213, 1);
x_215 = lean_ctor_get(x_214, 6);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_213, 0);
x_217 = lean_ctor_get(x_216, 6);
x_218 = lean_ctor_get(x_217, 25);
if (lean_obj_tag(x_218) == 0)
{
x_126 = x_212;
goto block_155;
}
else
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 0);
x_220 = lean_unbox(x_219);
x_200 = x_220;
x_201 = x_212;
goto block_211;
}
}
else
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_215, 0);
x_222 = lean_unbox(x_221);
x_200 = x_222;
x_201 = x_212;
goto block_211;
}
}
else
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_101, 0);
x_224 = lean_unbox(x_223);
x_200 = x_224;
x_201 = x_212;
goto block_211;
}
block_69:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_62);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lake_CacheMap_insertCore(x_55, x_66, x_60);
x_68 = lean_st_ref_set(x_63, x_67);
lean_dec(x_63);
x_40 = x_61;
x_41 = x_58;
x_42 = x_57;
x_43 = x_59;
x_44 = x_64;
goto block_50;
}
block_96:
{
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec_ref(x_71);
x_75 = lean_st_ref_take(x_74);
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
x_79 = lean_ctor_get_uint8(x_73, sizeof(void*)*3 + 1);
x_80 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_73, 2);
lean_inc(x_81);
lean_dec_ref(x_73);
x_82 = lean_ctor_get_uint64(x_76, sizeof(void*)*1);
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_string_utf8_byte_size(x_83);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = l_Lake_Hash_hex(x_82);
x_88 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_83);
x_57 = x_78;
x_58 = x_77;
x_59 = x_79;
x_60 = x_75;
x_61 = x_72;
x_62 = x_80;
x_63 = x_74;
x_64 = x_81;
x_65 = x_90;
goto block_69;
}
else
{
lean_object* x_91; 
x_91 = l_Lake_Hash_hex(x_82);
x_57 = x_78;
x_58 = x_77;
x_59 = x_79;
x_60 = x_75;
x_61 = x_72;
x_62 = x_80;
x_63 = x_74;
x_64 = x_81;
x_65 = x_91;
goto block_69;
}
}
else
{
lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_71);
x_92 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
x_94 = lean_ctor_get_uint8(x_73, sizeof(void*)*3 + 1);
x_95 = lean_ctor_get(x_73, 2);
lean_inc(x_95);
lean_dec_ref(x_73);
x_40 = x_72;
x_41 = x_92;
x_42 = x_93;
x_43 = x_94;
x_44 = x_95;
goto block_50;
}
}
block_100:
{
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_72 = x_98;
x_73 = x_99;
goto block_96;
}
else
{
lean_dec(x_71);
lean_dec_ref(x_22);
lean_del_object(x_19);
return x_97;
}
}
block_120:
{
lean_object* x_105; 
lean_inc_ref(x_11);
lean_inc_ref(x_22);
lean_inc_ref(x_1);
lean_inc(x_54);
x_105 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_6, x_55, x_52, x_54, x_1, x_22, x_103, x_7, x_8, x_9, x_10, x_11, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_8);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec_ref(x_106);
x_72 = x_108;
x_73 = x_107;
goto block_96;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_106);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec_ref(x_105);
lean_inc_ref(x_22);
x_110 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_17, x_22, x_7, x_8, x_9, x_10, x_11, x_109);
lean_dec_ref(x_17);
x_97 = x_110;
goto block_100;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_71);
lean_dec_ref(x_8);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
x_119 = !lean_is_exclusive(x_105);
if (x_119 == 0)
{
x_113 = x_105;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
block_125:
{
if (x_122 == 0)
{
lean_object* x_124; 
lean_dec(x_52);
lean_inc_ref(x_22);
x_124 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_17, x_22, x_7, x_8, x_9, x_10, x_11, x_123);
lean_dec_ref(x_17);
x_97 = x_124;
goto block_100;
}
else
{
x_103 = x_121;
x_104 = x_123;
goto block_120;
}
}
block_155:
{
lean_object* x_127; 
lean_inc(x_52);
x_127 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_17, x_52, x_56, x_8, x_9, x_10, x_11, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = 0;
x_131 = lean_unbox(x_128);
lean_dec(x_128);
x_132 = l_Lake_instDecidableEqOutputStatus(x_131, x_130);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_52);
lean_dec_ref(x_8);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_133 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_129);
lean_dec_ref(x_11);
x_97 = x_133;
goto block_100;
}
else
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_11, 1);
x_135 = lean_ctor_get(x_134, 1);
x_136 = lean_ctor_get(x_135, 6);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_134, 0);
x_138 = lean_ctor_get(x_137, 6);
x_139 = lean_ctor_get(x_138, 25);
if (lean_obj_tag(x_139) == 0)
{
x_103 = x_132;
x_104 = x_129;
goto block_120;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
x_141 = lean_unbox(x_140);
x_121 = x_132;
x_122 = x_141;
x_123 = x_129;
goto block_125;
}
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_136, 0);
x_143 = lean_unbox(x_142);
x_121 = x_132;
x_122 = x_143;
x_123 = x_129;
goto block_125;
}
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_101, 0);
x_145 = lean_unbox(x_144);
x_121 = x_132;
x_122 = x_145;
x_123 = x_129;
goto block_125;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_154; 
lean_dec(x_71);
lean_dec(x_52);
lean_dec_ref(x_8);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_127, 0);
x_147 = lean_ctor_get(x_127, 1);
x_154 = !lean_is_exclusive(x_127);
if (x_154 == 0)
{
x_148 = x_127;
x_149 = x_154;
goto block_153;
}
else
{
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_127);
x_148 = lean_box(0);
x_149 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_150; 
if (x_149 == 0)
{
x_150 = x_148;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_147);
x_150 = x_152;
goto block_151;
}
block_151:
{
return x_150;
}
}
}
}
block_195:
{
lean_object* x_158; 
lean_inc_ref(x_11);
lean_inc_ref(x_22);
lean_inc_ref(x_1);
lean_inc(x_54);
lean_inc(x_52);
x_158 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_6, x_55, x_52, x_54, x_1, x_22, x_157, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 1)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_54);
lean_dec_ref(x_8);
lean_dec(x_52);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
lean_dec_ref(x_159);
x_72 = x_161;
x_73 = x_160;
goto block_96;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_159);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec_ref(x_158);
x_163 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_17, x_52, x_56, x_8, x_9, x_10, x_11, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = 0;
x_167 = lean_unbox(x_164);
x_168 = l_Lake_instDecidableEqOutputStatus(x_167, x_166);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; 
lean_dec_ref(x_17);
lean_dec_ref(x_2);
x_169 = lean_box(0);
x_170 = lean_unbox(x_164);
lean_dec(x_164);
x_171 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_170, x_1, x_4, x_3, x_6, x_157, x_54, x_55, x_169, x_7, x_8, x_9, x_10, x_11, x_165);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_97 = x_171;
goto block_100;
}
else
{
lean_object* x_172; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_22);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_172 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_17, x_22, x_7, x_8, x_9, x_10, x_11, x_165);
lean_dec_ref(x_17);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_box(0);
x_175 = lean_unbox(x_164);
lean_dec(x_164);
x_176 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_175, x_1, x_4, x_3, x_6, x_157, x_54, x_55, x_174, x_7, x_8, x_9, x_10, x_11, x_173);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_97 = x_176;
goto block_100;
}
else
{
lean_dec(x_164);
lean_dec(x_71);
lean_dec(x_54);
lean_dec_ref(x_8);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_172;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_185; 
lean_dec(x_71);
lean_dec(x_54);
lean_dec_ref(x_8);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_163, 0);
x_178 = lean_ctor_get(x_163, 1);
x_185 = !lean_is_exclusive(x_163);
if (x_185 == 0)
{
x_179 = x_163;
x_180 = x_185;
goto block_184;
}
else
{
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_163);
x_179 = lean_box(0);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_180 == 0)
{
x_181 = x_179;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_178);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_194; 
lean_dec(x_71);
lean_dec(x_54);
lean_dec_ref(x_8);
lean_dec(x_52);
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_186 = lean_ctor_get(x_158, 0);
x_187 = lean_ctor_get(x_158, 1);
x_194 = !lean_is_exclusive(x_158);
if (x_194 == 0)
{
x_188 = x_158;
x_189 = x_194;
goto block_193;
}
else
{
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_158);
x_188 = lean_box(0);
x_189 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_190; 
if (x_189 == 0)
{
x_190 = x_188;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_186);
lean_ctor_set(x_192, 1, x_187);
x_190 = x_192;
goto block_191;
}
block_191:
{
return x_190;
}
}
}
}
block_199:
{
if (x_5 == 0)
{
x_156 = x_198;
x_157 = x_197;
goto block_195;
}
else
{
x_156 = x_198;
x_157 = x_196;
goto block_195;
}
}
block_211:
{
if (x_200 == 0)
{
x_126 = x_201;
goto block_155;
}
else
{
lean_inc(x_54);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_11, 1);
x_203 = lean_ctor_get(x_202, 0);
x_204 = lean_ctor_get(x_203, 6);
x_205 = lean_ctor_get(x_204, 26);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = 0;
x_196 = x_200;
x_197 = x_206;
x_198 = x_201;
goto block_199;
}
else
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_unbox(x_207);
x_196 = x_200;
x_197 = x_208;
x_198 = x_201;
goto block_199;
}
}
else
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_102, 0);
x_210 = lean_unbox(x_209);
x_196 = x_200;
x_197 = x_210;
x_198 = x_201;
goto block_199;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_del_object(x_19);
x_225 = lean_ctor_get(x_51, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_51, 1);
lean_inc(x_226);
lean_dec_ref(x_51);
x_227 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_17);
x_228 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_17);
lean_ctor_set(x_228, 2, x_18);
lean_ctor_set_uint8(x_228, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_228, sizeof(void*)*3 + 1, x_16);
x_229 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_17, x_225, x_227, x_8, x_9, x_10, x_11, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec_ref(x_229);
x_232 = 0;
x_233 = lean_unbox(x_230);
lean_dec(x_230);
x_234 = l_Lake_instDecidableEqOutputStatus(x_233, x_232);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_235 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_231);
lean_dec_ref(x_11);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_23 = x_236;
x_24 = x_237;
goto block_39;
}
else
{
lean_dec_ref(x_22);
return x_235;
}
}
else
{
lean_object* x_238; 
lean_inc_ref(x_22);
x_238 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_17, x_22, x_7, x_8, x_9, x_10, x_11, x_231);
lean_dec_ref(x_17);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_23 = x_239;
x_24 = x_240;
goto block_39;
}
else
{
lean_dec_ref(x_22);
return x_238;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_249; 
lean_dec_ref(x_22);
lean_dec_ref(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_241 = lean_ctor_get(x_229, 0);
x_242 = lean_ctor_get(x_229, 1);
x_249 = !lean_is_exclusive(x_229);
if (x_249 == 0)
{
x_243 = x_229;
x_244 = x_249;
goto block_248;
}
else
{
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_229);
x_243 = lean_box(0);
x_244 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_245; 
if (x_244 == 0)
{
x_245 = x_243;
goto block_246;
}
else
{
lean_object* x_247; 
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_242);
x_245 = x_247;
goto block_246;
}
block_246:
{
return x_245;
}
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_259; 
lean_dec_ref(x_22);
lean_del_object(x_19);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_51, 0);
x_251 = lean_ctor_get(x_51, 1);
x_259 = !lean_is_exclusive(x_51);
if (x_259 == 0)
{
x_252 = x_51;
x_253 = x_259;
goto block_258;
}
else
{
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_51);
x_252 = lean_box(0);
x_253 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_17);
lean_ctor_set(x_254, 2, x_18);
lean_ctor_set_uint8(x_254, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_254, sizeof(void*)*3 + 1, x_16);
if (x_253 == 0)
{
lean_ctor_set(x_252, 1, x_254);
x_255 = x_252;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_254);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
block_39:
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_37; 
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
x_27 = lean_ctor_get_uint8(x_24, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get(x_24, 2);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_24, 1);
lean_dec(x_38);
x_29 = x_24;
x_30 = x_37;
goto block_36;
}
else
{
lean_inc(x_28);
lean_inc(x_25);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lake_Artifact_trace(x_23);
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_31);
x_32 = x_29;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*3 + 1, x_27);
x_32 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_33; 
x_33 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(x_23, x_22, x_32);
lean_dec_ref(x_22);
return x_33;
}
}
}
block_50:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lake_Artifact_trace(x_40);
if (x_20 == 0)
{
lean_ctor_set(x_19, 2, x_44);
lean_ctor_set(x_19, 1, x_45);
lean_ctor_set(x_19, 0, x_41);
x_46 = x_19;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_44);
x_46 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_47; 
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_43);
x_47 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(x_40, x_22, x_46);
lean_dec_ref(x_22);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_7(x_1, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_51; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_ctor_get(x_14, 2);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
x_21 = x_14;
x_22 = x_51;
goto block_50;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_BuildTrace_mix(x_19, x_15);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_23);
x_24 = x_21;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_23);
lean_ctor_set(x_49, 2, x_20);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_18);
x_24 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_apply_1(x_2, x_5);
x_26 = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
x_27 = 0;
x_28 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_25, x_4, x_26, x_27, x_27, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_38; 
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
x_31 = x_28;
x_32 = x_38;
goto block_37;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_33);
lean_dec(x_29);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_33);
x_34 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_30);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
x_41 = x_28;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
x_54 = x_13;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lake_buildFileAfterDep___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lake_instDataKindFilePath;
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_Lake_Job_mapM___redArg(x_15, x_2, x_14, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildFileAfterDep___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lake_instDataKindFilePath;
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l_Lake_Job_mapM___redArg(x_16, x_3, x_15, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildFileAfterDep(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_io_metadata(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_17; 
x_6 = lean_ctor_get(x_5, 0);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
x_7 = x_5;
x_8 = x_17;
goto block_16;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_11 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_12);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_5, 0);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
x_19 = x_5;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_3, 0);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
x_27 = x_3;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
x_14 = x_7;
x_15 = x_33;
goto block_32;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_17);
x_18 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_11);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec_ref(x_16);
x_23 = lean_io_error_to_string(x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_9);
x_27 = lean_array_push(x_9, x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_27);
x_28 = x_14;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_13);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_11);
x_28 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_instDataKindFilePath;
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
x_12 = l_Lake_Job_async___redArg(x_9, x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_io_metadata(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_17; 
x_6 = lean_ctor_get(x_5, 0);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
x_7 = x_5;
x_8 = x_17;
goto block_16;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec(x_6);
x_10 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_11 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_12);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_5, 0);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
x_19 = x_5;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_3, 0);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
x_27 = x_3;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
x_14 = x_7;
x_15 = x_33;
goto block_32;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_17);
x_18 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_11);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec_ref(x_16);
x_23 = lean_io_error_to_string(x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_9);
x_27 = lean_array_push(x_9, x_25);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_27);
x_28 = x_14;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_13);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_11);
x_28 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_instDataKindFilePath;
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
x_12 = l_Lake_Job_async___redArg(x_9, x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_inputFile___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_10; 
x_10 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_inputFile(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_inputDir___lam__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_3);
x_16 = l_System_FilePath_isDir(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_1);
lean_inc(x_15);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
x_8 = x_5;
x_9 = x_6;
goto block_13;
}
else
{
lean_object* x_19; 
lean_inc(x_15);
x_19 = lean_array_push(x_5, x_15);
x_8 = x_19;
x_9 = x_6;
goto block_13;
}
}
else
{
x_8 = x_5;
x_9 = x_6;
goto block_13;
}
}
else
{
lean_object* x_20; 
lean_dec_ref(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_31 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_32 = lean_ctor_get(x_9, 1);
x_33 = lean_ctor_get(x_9, 2);
x_34 = l_System_FilePath_walkDir(x_1, x_2);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_45; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get_size(x_35);
x_50 = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
x_51 = lean_nat_dec_lt(x_36, x_49);
if (x_51 == 0)
{
lean_dec(x_35);
lean_dec_ref(x_3);
x_37 = x_50;
x_38 = x_9;
goto block_44;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
if (x_51 == 0)
{
lean_dec(x_35);
lean_dec_ref(x_3);
x_37 = x_50;
x_38 = x_9;
goto block_44;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_35, x_53, x_54, x_50, x_9);
lean_dec(x_35);
x_45 = x_55;
goto block_48;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_49);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_35, x_56, x_57, x_50, x_9);
lean_dec(x_35);
x_45 = x_58;
goto block_48;
}
}
block_44:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_get_size(x_37);
x_40 = lean_nat_dec_eq(x_39, x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_39, x_41);
x_43 = lean_nat_dec_le(x_36, x_42);
if (x_43 == 0)
{
lean_inc(x_42);
x_22 = x_39;
x_23 = x_42;
x_24 = x_37;
x_25 = x_38;
x_26 = x_42;
goto block_28;
}
else
{
x_22 = x_39;
x_23 = x_42;
x_24 = x_37;
x_25 = x_38;
x_26 = x_36;
goto block_28;
}
}
else
{
x_11 = x_38;
x_12 = x_37;
goto block_14;
}
}
block_48:
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_37 = x_46;
x_38 = x_47;
goto block_44;
}
else
{
return x_45;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; uint8_t x_72; 
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_29);
lean_dec_ref(x_3);
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_9, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_9, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_9, 0);
lean_dec(x_75);
x_59 = x_9;
x_60 = x_72;
goto block_71;
}
else
{
lean_dec(x_9);
x_59 = lean_box(0);
x_60 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec_ref(x_34);
x_62 = lean_io_error_to_string(x_61);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_29);
x_66 = lean_array_push(x_29, x_64);
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_66);
x_67 = x_59;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_32);
lean_ctor_set(x_70, 2, x_33);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_30);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 1, x_31);
x_67 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_18, x_16, x_19);
lean_dec(x_19);
x_11 = x_17;
x_12 = x_20;
goto block_14;
}
block_28:
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_26, x_23);
if (x_27 == 0)
{
lean_dec(x_23);
lean_inc(x_26);
x_15 = x_22;
x_16 = x_26;
x_17 = x_25;
x_18 = x_24;
x_19 = x_26;
goto block_21;
}
else
{
x_15 = x_22;
x_16 = x_26;
x_17 = x_25;
x_18 = x_24;
x_19 = x_23;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_inputDir___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
if (x_1 == 0)
{
lean_object* x_23; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = l_Lake_inputBinFile___redArg(x_14, x_5, x_6, x_7, x_8, x_9);
x_17 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l_Lake_inputTextFile___redArg(x_14, x_5, x_6, x_7, x_8, x_9);
x_17 = x_24;
goto block_22;
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_16, x_3, x_17);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_3);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_16 = x_13;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lake_Job_collectArray___redArg(x_14, x_2);
lean_dec(x_14);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_15);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_26 = x_13;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lake_inputDir___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_16 = l_Lake_Job_async___redArg(x_13, x_12, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
x_17 = lean_box(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = 0;
x_20 = l_Lake_Job_bindM___redArg(x_13, x_16, x_18, x_14, x_19, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputDir(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = l_Lake_Hash_nil;
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_uint64_mix_hash(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Lake_buildO___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_45; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
x_17 = x_10;
x_18 = x_45;
goto block_44;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_19; 
x_19 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_31; 
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
x_22 = x_19;
x_23 = x_31;
goto block_30;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_24; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_21);
x_24 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_14);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_43; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
x_34 = x_19;
x_35 = x_43;
goto block_42;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_box(0);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_33);
x_36 = x_17;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_15);
lean_ctor_set(x_41, 2, x_16);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_41, sizeof(void*)*3 + 1, x_14);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_buildO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void) {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_106; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_15, 2);
x_106 = !lean_is_exclusive(x_15);
if (x_106 == 0)
{
x_22 = x_15;
x_23 = x_106;
goto block_105;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_24 = l_Lake_platformTrace;
x_25 = l_Lake_BuildTrace_mix(x_20, x_24);
x_90 = l_Lake_Hash_nil;
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_array_get_size(x_1);
x_93 = lean_nat_dec_lt(x_91, x_92);
if (x_93 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_26 = x_90;
goto block_89;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_92, x_92);
if (x_94 == 0)
{
if (x_93 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_26 = x_90;
goto block_89;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; uint64_t x_99; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_92);
x_97 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_95, x_96, x_97);
x_99 = lean_unbox_uint64(x_98);
lean_dec(x_98);
x_26 = x_99;
goto block_89;
}
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; 
x_100 = 0;
x_101 = lean_usize_of_nat(x_92);
x_102 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_103 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_100, x_101, x_102);
x_104 = lean_unbox_uint64(x_103);
lean_dec(x_103);
x_26 = x_104;
goto block_89;
}
}
block_89:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_28 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(x_1);
x_29 = lean_array_to_list(x_1);
x_30 = l_List_toString___redArg(x_2, x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec_ref(x_30);
x_32 = lean_string_append(x_27, x_31);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_34 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_35 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*3, x_26);
x_36 = l_Lake_BuildTrace_mix(x_25, x_35);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_36);
x_37 = x_22;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_88, 0, x_17);
lean_ctor_set(x_88, 1, x_36);
lean_ctor_set(x_88, 2, x_21);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 1, x_19);
x_37 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_38; 
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_38 = lean_apply_7(x_3, x_10, x_11, x_12, x_13, x_14, x_37, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_77; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
x_43 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 1);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_77 = !lean_is_exclusive(x_39);
if (x_77 == 0)
{
x_46 = x_39;
x_47 = x_77;
goto block_76;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_41);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lake_BuildTrace_mix(x_44, x_40);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_48);
x_49 = x_46;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_48);
lean_ctor_set(x_75, 2, x_45);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_42);
lean_ctor_set_uint8(x_75, sizeof(void*)*3 + 1, x_43);
x_49 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_51 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_51, 0, x_5);
lean_closure_set(x_51, 1, x_9);
lean_closure_set(x_51, 2, x_50);
lean_closure_set(x_51, 3, x_6);
x_52 = 0;
x_53 = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
x_54 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_51, x_52, x_53, x_52, x_52, x_10, x_11, x_12, x_13, x_14, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_64; 
x_55 = lean_ctor_get(x_54, 0);
x_56 = lean_ctor_get(x_54, 1);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
x_57 = x_54;
x_58 = x_64;
goto block_63;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_59);
lean_dec(x_55);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_59);
x_60 = x_57;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_56);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
x_73 = !lean_is_exclusive(x_54);
if (x_73 == 0)
{
x_67 = x_54;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_78 = lean_ctor_get(x_38, 0);
x_79 = lean_ctor_get(x_38, 1);
x_86 = !lean_is_exclusive(x_38);
if (x_86 == 0)
{
x_80 = x_38;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_38);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lake_buildO___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = ((lean_object*)(l_Lake_buildO___closed__0));
x_15 = l_Lake_instDataKindFilePath;
x_16 = ((lean_object*)(l_Lake_buildO___closed__1));
x_17 = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
x_18 = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_17);
lean_closure_set(x_18, 7, x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 0;
x_21 = l_Lake_Job_mapM___redArg(x_15, x_2, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_60; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 2);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
x_20 = x_11;
x_21 = x_60;
goto block_59;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_15);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_57);
x_23 = x_57;
goto block_56;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_5, 0);
lean_inc(x_58);
lean_dec_ref(x_5);
x_23 = x_58;
goto block_56;
}
block_56:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 13);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_22, 17);
lean_inc_ref(x_25);
lean_dec_ref(x_22);
x_26 = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
x_27 = lean_array_push(x_26, x_23);
x_28 = l_Array_append___redArg(x_27, x_25);
lean_dec_ref(x_25);
x_29 = l_Array_append___redArg(x_28, x_1);
x_30 = l_Array_append___redArg(x_29, x_2);
x_31 = l_Lake_compileO(x_3, x_4, x_30, x_24, x_15);
lean_dec_ref(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_43; 
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
x_34 = x_31;
x_35 = x_43;
goto block_42;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_33);
x_36 = x_20;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_18);
lean_ctor_set(x_41, 2, x_19);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_41, sizeof(void*)*3 + 1, x_17);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_55; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
x_46 = x_31;
x_47 = x_55;
goto block_54;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_box(0);
x_47 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_48; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_45);
x_48 = x_20;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_18);
lean_ctor_set(x_53, 2, x_19);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_17);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_48);
x_49 = x_46;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Lake_Hash_nil;
x_8 = lean_string_hash(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec_ref(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
x_6 = lean_string_append(x_5, x_4);
x_7 = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(x_11, x_3);
x_13 = 93;
x_14 = lean_string_push(x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_74; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_74 = !lean_is_exclusive(x_11);
if (x_74 == 0)
{
x_18 = x_11;
x_19 = x_74;
goto block_73;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_13);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_20 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_4);
lean_inc_ref(x_20);
x_22 = l_Lake_BuildTrace_mix(x_16, x_20);
x_62 = l_Lake_Hash_nil;
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_array_get_size(x_2);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
x_23 = x_62;
goto block_61;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_64, x_64);
if (x_66 == 0)
{
if (x_65 == 0)
{
x_23 = x_62;
goto block_61;
}
else
{
size_t x_67; size_t x_68; uint64_t x_69; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_64);
x_69 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_67, x_68, x_62);
x_23 = x_69;
goto block_61;
}
}
else
{
size_t x_70; size_t x_71; uint64_t x_72; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_64);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_70, x_71, x_62);
x_23 = x_72;
goto block_61;
}
}
block_61:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_25 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_26 = lean_array_to_list(x_2);
x_27 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_31 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_32 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint64(x_32, sizeof(void*)*3, x_23);
x_33 = l_Lake_BuildTrace_mix(x_22, x_32);
x_34 = l_Lake_platformTrace;
x_35 = l_Lake_BuildTrace_mix(x_33, x_34);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_35);
x_36 = x_18;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_35);
lean_ctor_set(x_60, 2, x_17);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_14);
lean_ctor_set_uint8(x_60, sizeof(void*)*3 + 1, x_15);
x_36 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
x_38 = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
x_39 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_21, x_37, x_38, x_37, x_37, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_49; 
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 1);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
x_42 = x_39;
x_43 = x_49;
goto block_48;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_44);
lean_dec(x_40);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_44);
x_45 = x_42;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_41);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
x_58 = !lean_is_exclusive(x_39);
if (x_58 == 0)
{
x_52 = x_39;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_Job_mapM___redArg(x_14, x_2, x_13, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_48; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
x_19 = x_9;
x_20 = x_48;
goto block_47;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 12);
lean_inc_ref(x_21);
lean_dec_ref(x_13);
x_22 = l_Lake_compileStaticLib(x_1, x_2, x_21, x_3, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 1);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
x_25 = x_22;
x_26 = x_34;
goto block_33;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_27; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_24);
x_27 = x_19;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 1, x_16);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_27);
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_46; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
x_37 = x_22;
x_38 = x_46;
goto block_45;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_box(0);
x_38 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_39; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_36);
x_39 = x_19;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_16);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_39);
x_40 = x_37;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_box(x_2);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_11);
x_13 = 0;
x_14 = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
x_15 = 1;
x_16 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_12, x_13, x_14, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
x_19 = x_16;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_21);
lean_dec(x_17);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_18);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
x_29 = x_16;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_buildStaticLib___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_instDataKindFilePath;
x_14 = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
x_15 = l_Lake_Job_collectArray___redArg(x_2, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_Lake_Job_mapM___redArg(x_13, x_15, x_12, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_6);
x_7 = lean_array_push(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_16; 
x_6 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_6);
x_16 = l_Lake_Dynlib_dir_x3f(x_6);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_array_push(x_4, x_19);
x_7 = x_20;
goto block_15;
}
else
{
lean_dec(x_16);
x_7 = x_4;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
x_10 = lean_string_append(x_9, x_8);
x_11 = lean_array_push(x_7, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_3 = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_4, x_5, x_3);
x_7 = lean_array_size(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_2, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_string_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_289; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_289 = !lean_is_exclusive(x_3);
if (x_289 == 0)
{
x_9 = x_3;
x_10 = x_289;
goto block_288;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_11; 
x_11 = lean_string_dec_lt(x_1, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_1, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_8);
x_14 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 4);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_mul(x_21, x_15);
x_23 = lean_nat_dec_lt(x_22, x_16);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_24 = lean_nat_add(x_14, x_15);
x_25 = lean_nat_add(x_24, x_16);
lean_dec(x_16);
lean_dec(x_24);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 0, x_25);
x_26 = x_9;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 3, x_7);
lean_ctor_set(x_28, 4, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_92; 
x_92 = !lean_is_exclusive(x_13);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_13, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_13, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_13, 2);
lean_dec(x_95);
x_96 = lean_ctor_get(x_13, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_13, 0);
lean_dec(x_97);
x_29 = x_13;
x_30 = x_92;
goto block_91;
}
else
{
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_mul(x_37, x_36);
x_39 = lean_nat_dec_lt(x_31, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_67; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_19, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_19, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_19, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_19, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_40 = x_19;
x_41 = x_67;
goto block_66;
}
else
{
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_55; 
x_42 = lean_nat_add(x_14, x_15);
x_43 = lean_nat_add(x_42, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_34, 0);
lean_inc(x_64);
x_55 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_unsigned_to_nat(0u);
x_55 = x_65;
goto block_63;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_20);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 2, x_18);
lean_ctor_set(x_40, 1, x_17);
lean_ctor_set(x_40, 0, x_47);
x_48 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set(x_53, 2, x_18);
lean_ctor_set(x_53, 3, x_35);
lean_ctor_set(x_53, 4, x_20);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_48);
lean_ctor_set(x_29, 3, x_44);
lean_ctor_set(x_29, 2, x_33);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_29, 0, x_43);
x_49 = x_29;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_32);
lean_ctor_set(x_51, 2, x_33);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set(x_51, 4, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
block_63:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_add(x_42, x_55);
lean_dec(x_55);
lean_dec(x_42);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_34);
lean_ctor_set(x_9, 0, x_56);
x_57 = x_9;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_5);
lean_ctor_set(x_62, 2, x_6);
lean_ctor_set(x_62, 3, x_7);
lean_ctor_set(x_62, 4, x_34);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
x_58 = lean_nat_add(x_14, x_36);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
x_44 = x_57;
x_45 = x_58;
x_46 = x_59;
goto block_54;
}
else
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(0u);
x_44 = x_57;
x_45 = x_58;
x_46 = x_60;
goto block_54;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_del_object(x_9);
x_73 = lean_nat_add(x_14, x_15);
x_74 = lean_nat_add(x_73, x_16);
lean_dec(x_16);
x_75 = lean_nat_add(x_73, x_31);
lean_dec(x_73);
lean_inc_ref(x_7);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 3, x_7);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 0, x_75);
x_76 = x_29;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_90, 2, x_6);
lean_ctor_set(x_90, 3, x_7);
lean_ctor_set(x_90, 4, x_19);
x_76 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_77; uint8_t x_78; uint8_t x_83; 
x_83 = !lean_is_exclusive(x_7);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_7, 4);
lean_dec(x_84);
x_85 = lean_ctor_get(x_7, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_7, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_7, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_7, 0);
lean_dec(x_88);
x_77 = x_7;
x_78 = x_83;
goto block_82;
}
else
{
lean_dec(x_7);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
lean_ctor_set(x_77, 4, x_20);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 2, x_18);
lean_ctor_set(x_77, 1, x_17);
lean_ctor_set(x_77, 0, x_74);
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_17);
lean_ctor_set(x_81, 2, x_18);
lean_ctor_set(x_81, 3, x_76);
lean_ctor_set(x_81, 4, x_20);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_13, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_124; 
x_99 = lean_ctor_get(x_13, 4);
x_100 = lean_ctor_get(x_13, 1);
x_101 = lean_ctor_get(x_13, 2);
x_124 = !lean_is_exclusive(x_13);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_13, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_13, 0);
lean_dec(x_126);
x_102 = x_13;
x_103 = x_124;
goto block_123;
}
else
{
lean_inc(x_99);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_13);
x_102 = lean_box(0);
x_103 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_119; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_119 = !lean_is_exclusive(x_98);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_98, 4);
lean_dec(x_120);
x_121 = lean_ctor_get(x_98, 3);
lean_dec(x_121);
x_122 = lean_ctor_get(x_98, 0);
lean_dec(x_122);
x_106 = x_98;
x_107 = x_119;
goto block_118;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = lean_box(0);
x_107 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(3u);
lean_inc_n(x_99, 2);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_99);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 0, x_14);
x_109 = x_106;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_14);
lean_ctor_set(x_117, 1, x_5);
lean_ctor_set(x_117, 2, x_6);
lean_ctor_set(x_117, 3, x_99);
lean_ctor_set(x_117, 4, x_99);
x_109 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_110; 
lean_inc(x_99);
if (x_103 == 0)
{
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 0, x_14);
x_110 = x_102;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_14);
lean_ctor_set(x_115, 1, x_100);
lean_ctor_set(x_115, 2, x_101);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_99);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_110);
lean_ctor_set(x_9, 3, x_109);
lean_ctor_set(x_9, 2, x_105);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_108);
x_111 = x_9;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_105);
lean_ctor_set(x_113, 3, x_109);
lean_ctor_set(x_113, 4, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_13, 4);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_140; 
x_128 = lean_ctor_get(x_13, 1);
x_129 = lean_ctor_get(x_13, 2);
x_140 = !lean_is_exclusive(x_13);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_13, 4);
lean_dec(x_141);
x_142 = lean_ctor_get(x_13, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_13, 0);
lean_dec(x_143);
x_130 = x_13;
x_131 = x_140;
goto block_139;
}
else
{
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_13);
x_130 = lean_box(0);
x_131 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_unsigned_to_nat(3u);
if (x_131 == 0)
{
lean_ctor_set(x_130, 4, x_98);
lean_ctor_set(x_130, 2, x_6);
lean_ctor_set(x_130, 1, x_5);
lean_ctor_set(x_130, 0, x_14);
x_133 = x_130;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_14);
lean_ctor_set(x_138, 1, x_5);
lean_ctor_set(x_138, 2, x_6);
lean_ctor_set(x_138, 3, x_98);
lean_ctor_set(x_138, 4, x_98);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_127);
lean_ctor_set(x_9, 3, x_133);
lean_ctor_set(x_9, 2, x_129);
lean_ctor_set(x_9, 1, x_128);
lean_ctor_set(x_9, 0, x_132);
x_134 = x_9;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_127);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_13);
lean_ctor_set(x_9, 3, x_127);
lean_ctor_set(x_9, 0, x_144);
x_145 = x_9;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_5);
lean_ctor_set(x_147, 2, x_6);
lean_ctor_set(x_147, 3, x_127);
lean_ctor_set(x_147, 4, x_13);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
x_148 = x_9;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_1);
lean_ctor_set(x_150, 2, x_2);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_8);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_4);
x_151 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_7);
x_152 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_153 = lean_ctor_get(x_8, 0);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
x_159 = lean_unsigned_to_nat(3u);
x_160 = lean_nat_mul(x_159, x_153);
x_161 = lean_nat_dec_lt(x_160, x_154);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
x_162 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_163 = lean_nat_add(x_162, x_153);
lean_dec(x_162);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_163);
x_164 = x_9;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 2, x_6);
lean_ctor_set(x_166, 3, x_151);
lean_ctor_set(x_166, 4, x_8);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
else
{
lean_object* x_167; uint8_t x_168; uint8_t x_232; 
x_232 = !lean_is_exclusive(x_151);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_151, 4);
lean_dec(x_233);
x_234 = lean_ctor_get(x_151, 3);
lean_dec(x_234);
x_235 = lean_ctor_get(x_151, 2);
lean_dec(x_235);
x_236 = lean_ctor_get(x_151, 1);
lean_dec(x_236);
x_237 = lean_ctor_get(x_151, 0);
lean_dec(x_237);
x_167 = x_151;
x_168 = x_232;
goto block_231;
}
else
{
lean_dec(x_151);
x_167 = lean_box(0);
x_168 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_169 = lean_ctor_get(x_157, 0);
x_170 = lean_ctor_get(x_158, 0);
x_171 = lean_ctor_get(x_158, 1);
x_172 = lean_ctor_get(x_158, 2);
x_173 = lean_ctor_get(x_158, 3);
x_174 = lean_ctor_get(x_158, 4);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_mul(x_175, x_169);
x_177 = lean_nat_dec_lt(x_170, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; uint8_t x_206; 
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
x_206 = !lean_is_exclusive(x_158);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_158, 4);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_158, 0);
lean_dec(x_211);
x_178 = x_158;
x_179 = x_206;
goto block_205;
}
else
{
lean_dec(x_158);
x_178 = lean_box(0);
x_179 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_193; lean_object* x_194; 
x_180 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_181 = lean_nat_add(x_180, x_153);
lean_dec(x_180);
x_193 = lean_nat_add(x_152, x_169);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_173, 0);
lean_inc(x_203);
x_194 = x_203;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = lean_unsigned_to_nat(0u);
x_194 = x_204;
goto block_202;
}
block_192:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_nat_add(x_182, x_184);
lean_dec(x_184);
lean_dec(x_182);
if (x_179 == 0)
{
lean_ctor_set(x_178, 4, x_8);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 2, x_6);
lean_ctor_set(x_178, 1, x_5);
lean_ctor_set(x_178, 0, x_185);
x_186 = x_178;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_185);
lean_ctor_set(x_191, 1, x_5);
lean_ctor_set(x_191, 2, x_6);
lean_ctor_set(x_191, 3, x_174);
lean_ctor_set(x_191, 4, x_8);
x_186 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_187; 
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_186);
lean_ctor_set(x_167, 3, x_183);
lean_ctor_set(x_167, 2, x_172);
lean_ctor_set(x_167, 1, x_171);
lean_ctor_set(x_167, 0, x_181);
x_187 = x_167;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_181);
lean_ctor_set(x_189, 1, x_171);
lean_ctor_set(x_189, 2, x_172);
lean_ctor_set(x_189, 3, x_183);
lean_ctor_set(x_189, 4, x_186);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
block_202:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_nat_add(x_193, x_194);
lean_dec(x_194);
lean_dec(x_193);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_173);
lean_ctor_set(x_9, 3, x_157);
lean_ctor_set(x_9, 2, x_156);
lean_ctor_set(x_9, 1, x_155);
lean_ctor_set(x_9, 0, x_195);
x_196 = x_9;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_155);
lean_ctor_set(x_201, 2, x_156);
lean_ctor_set(x_201, 3, x_157);
lean_ctor_set(x_201, 4, x_173);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
x_197 = lean_nat_add(x_152, x_153);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_174, 0);
lean_inc(x_198);
x_182 = x_197;
x_183 = x_196;
x_184 = x_198;
goto block_192;
}
else
{
lean_object* x_199; 
x_199 = lean_unsigned_to_nat(0u);
x_182 = x_197;
x_183 = x_196;
x_184 = x_199;
goto block_192;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_del_object(x_9);
x_212 = lean_nat_add(x_152, x_154);
lean_dec(x_154);
x_213 = lean_nat_add(x_212, x_153);
lean_dec(x_212);
x_214 = lean_nat_add(x_152, x_153);
x_215 = lean_nat_add(x_214, x_170);
lean_dec(x_214);
lean_inc_ref(x_8);
if (x_168 == 0)
{
lean_ctor_set(x_167, 4, x_8);
lean_ctor_set(x_167, 3, x_158);
lean_ctor_set(x_167, 2, x_6);
lean_ctor_set(x_167, 1, x_5);
lean_ctor_set(x_167, 0, x_215);
x_216 = x_167;
goto block_229;
}
else
{
lean_object* x_230; 
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_215);
lean_ctor_set(x_230, 1, x_5);
lean_ctor_set(x_230, 2, x_6);
lean_ctor_set(x_230, 3, x_158);
lean_ctor_set(x_230, 4, x_8);
x_216 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_217; uint8_t x_218; uint8_t x_223; 
x_223 = !lean_is_exclusive(x_8);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_8, 4);
lean_dec(x_224);
x_225 = lean_ctor_get(x_8, 3);
lean_dec(x_225);
x_226 = lean_ctor_get(x_8, 2);
lean_dec(x_226);
x_227 = lean_ctor_get(x_8, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_8, 0);
lean_dec(x_228);
x_217 = x_8;
x_218 = x_223;
goto block_222;
}
else
{
lean_dec(x_8);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
lean_ctor_set(x_217, 4, x_216);
lean_ctor_set(x_217, 3, x_157);
lean_ctor_set(x_217, 2, x_156);
lean_ctor_set(x_217, 1, x_155);
lean_ctor_set(x_217, 0, x_213);
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_155);
lean_ctor_set(x_221, 2, x_156);
lean_ctor_set(x_221, 3, x_157);
lean_ctor_set(x_221, 4, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
}
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_151, 3);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_252; 
x_239 = lean_ctor_get(x_151, 4);
x_240 = lean_ctor_get(x_151, 1);
x_241 = lean_ctor_get(x_151, 2);
x_252 = !lean_is_exclusive(x_151);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_151, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_151, 0);
lean_dec(x_254);
x_242 = x_151;
x_243 = x_252;
goto block_251;
}
else
{
lean_inc(x_239);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_151);
x_242 = lean_box(0);
x_243 = x_252;
goto block_251;
}
block_251:
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_unsigned_to_nat(3u);
lean_inc(x_239);
if (x_243 == 0)
{
lean_ctor_set(x_242, 3, x_239);
lean_ctor_set(x_242, 2, x_6);
lean_ctor_set(x_242, 1, x_5);
lean_ctor_set(x_242, 0, x_152);
x_245 = x_242;
goto block_249;
}
else
{
lean_object* x_250; 
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_152);
lean_ctor_set(x_250, 1, x_5);
lean_ctor_set(x_250, 2, x_6);
lean_ctor_set(x_250, 3, x_239);
lean_ctor_set(x_250, 4, x_239);
x_245 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_246; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_245);
lean_ctor_set(x_9, 3, x_238);
lean_ctor_set(x_9, 2, x_241);
lean_ctor_set(x_9, 1, x_240);
lean_ctor_set(x_9, 0, x_244);
x_246 = x_9;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_240);
lean_ctor_set(x_248, 2, x_241);
lean_ctor_set(x_248, 3, x_238);
lean_ctor_set(x_248, 4, x_245);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_151, 4);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_280; 
x_256 = lean_ctor_get(x_151, 1);
x_257 = lean_ctor_get(x_151, 2);
x_280 = !lean_is_exclusive(x_151);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_151, 4);
lean_dec(x_281);
x_282 = lean_ctor_get(x_151, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_151, 0);
lean_dec(x_283);
x_258 = x_151;
x_259 = x_280;
goto block_279;
}
else
{
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_151);
x_258 = lean_box(0);
x_259 = x_280;
goto block_279;
}
block_279:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_275; 
x_260 = lean_ctor_get(x_255, 1);
x_261 = lean_ctor_get(x_255, 2);
x_275 = !lean_is_exclusive(x_255);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_255, 4);
lean_dec(x_276);
x_277 = lean_ctor_get(x_255, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_255, 0);
lean_dec(x_278);
x_262 = x_255;
x_263 = x_275;
goto block_274;
}
else
{
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_255);
x_262 = lean_box(0);
x_263 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_unsigned_to_nat(3u);
if (x_263 == 0)
{
lean_ctor_set(x_262, 4, x_238);
lean_ctor_set(x_262, 3, x_238);
lean_ctor_set(x_262, 2, x_257);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set(x_262, 0, x_152);
x_265 = x_262;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_152);
lean_ctor_set(x_273, 1, x_256);
lean_ctor_set(x_273, 2, x_257);
lean_ctor_set(x_273, 3, x_238);
lean_ctor_set(x_273, 4, x_238);
x_265 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_266; 
if (x_259 == 0)
{
lean_ctor_set(x_258, 4, x_238);
lean_ctor_set(x_258, 2, x_6);
lean_ctor_set(x_258, 1, x_5);
lean_ctor_set(x_258, 0, x_152);
x_266 = x_258;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_271, 0, x_152);
lean_ctor_set(x_271, 1, x_5);
lean_ctor_set(x_271, 2, x_6);
lean_ctor_set(x_271, 3, x_238);
lean_ctor_set(x_271, 4, x_238);
x_266 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_267; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_266);
lean_ctor_set(x_9, 3, x_265);
lean_ctor_set(x_9, 2, x_261);
lean_ctor_set(x_9, 1, x_260);
lean_ctor_set(x_9, 0, x_264);
x_267 = x_9;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_269, 0, x_264);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_261);
lean_ctor_set(x_269, 3, x_265);
lean_ctor_set(x_269, 4, x_266);
x_267 = x_269;
goto block_268;
}
block_268:
{
return x_267;
}
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_255);
lean_ctor_set(x_9, 3, x_151);
lean_ctor_set(x_9, 0, x_284);
x_285 = x_9;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_5);
lean_ctor_set(x_287, 2, x_6);
lean_ctor_set(x_287, 3, x_151);
lean_ctor_set(x_287, 4, x_255);
x_285 = x_287;
goto block_286;
}
block_286:
{
return x_285;
}
}
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(1u);
x_291 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_1);
lean_ctor_set(x_291, 2, x_2);
lean_ctor_set(x_291, 3, x_3);
lean_ctor_set(x_291, 4, x_3);
return x_291;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_array_push(x_4, x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
if (x_8 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_5, x_26, x_3);
x_11 = x_27;
goto block_25;
}
else
{
lean_dec_ref(x_5);
x_11 = x_3;
goto block_25;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
if (x_15 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_14);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_10, x_6, x_19, x_20, x_12);
lean_dec_ref(x_6);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_10, x_6, x_22, x_23, x_12);
lean_dec_ref(x_6);
return x_24;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_7);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_1);
lean_inc(x_9);
x_10 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(x_9, x_1, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
x_6 = x_1;
x_7 = x_15;
goto block_14;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
x_9 = lean_string_append(x_8, x_4);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_2);
x_10 = x_13;
goto block_12;
}
block_12:
{
x_1 = x_5;
x_2 = x_10;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1));
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_array_uget_borrowed(x_1, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(x_8, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_7; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
x_34 = lean_array_get_size(x_1);
x_35 = lean_nat_dec_lt(x_32, x_34);
if (x_35 == 0)
{
x_4 = x_33;
goto block_6;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
if (x_35 == 0)
{
x_4 = x_33;
goto block_6;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_38, x_39, x_36);
x_7 = x_40;
goto block_31;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_34);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_41, x_42, x_36);
x_7 = x_43;
goto block_31;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
block_31:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_28; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_14 = x_2;
x_15 = x_28;
goto block_27;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
x_17 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_8);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_9);
x_22 = lean_array_push(x_9, x_20);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_22);
x_23 = x_14;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_11);
x_23 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec_ref(x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_4 = x_30;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_50; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
x_19 = x_12;
x_20 = x_50;
goto block_49;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_22 = l_Array_append___redArg(x_21, x_2);
x_23 = l_Array_append___redArg(x_22, x_3);
x_24 = l_Lake_compileSharedLib(x_4, x_23, x_5, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
x_27 = x_24;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_29; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_26);
x_29 = x_19;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_17);
lean_ctor_set(x_34, 2, x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_16);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_29);
x_30 = x_27;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_48; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
x_39 = x_24;
x_40 = x_48;
goto block_47;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_box(0);
x_40 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_41; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_38);
x_41 = x_19;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_17);
lean_ctor_set(x_46, 2, x_18);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_16);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_41);
x_42 = x_39;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildSharedLib___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_empty_array_with_capacity(x_2);
x_13 = lean_apply_8(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_4, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_apply_8(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_16, lean_box(0));
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
x_20 = x_14;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lake_buildSharedLib___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint64_t x_16; uint64_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = l_Lake_Hash_nil;
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_1);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
x_16 = x_94;
goto block_93;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
if (x_97 == 0)
{
x_16 = x_94;
goto block_93;
}
else
{
size_t x_99; size_t x_100; uint64_t x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_96);
x_101 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_99, x_100, x_94);
x_16 = x_101;
goto block_93;
}
}
else
{
size_t x_102; size_t x_103; uint64_t x_104; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_96);
x_104 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_102, x_103, x_94);
x_16 = x_104;
goto block_93;
}
}
block_93:
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_92; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_14, 2);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
x_22 = x_14;
x_23 = x_92;
goto block_91;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_26 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_27 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_28 = lean_array_to_list(x_1);
x_29 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_26, x_30);
lean_dec_ref(x_30);
x_32 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_33 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_16);
x_34 = l_Lake_BuildTrace_mix(x_20, x_33);
x_35 = l_Lake_platformTrace;
x_36 = l_Lake_BuildTrace_mix(x_34, x_35);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_36);
x_37 = x_22;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_36);
lean_ctor_set(x_90, 2, x_21);
lean_ctor_set_uint8(x_90, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_90, sizeof(void*)*3 + 1, x_19);
x_37 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_38; 
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_38 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_37, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_79; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
x_43 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 1);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_79 = !lean_is_exclusive(x_39);
if (x_79 == 0)
{
x_46 = x_39;
x_47 = x_79;
goto block_78;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_41);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_box(x_3);
lean_inc_ref(x_8);
x_49 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_49, 0, x_48);
lean_closure_set(x_49, 1, x_24);
lean_closure_set(x_49, 2, x_4);
lean_closure_set(x_49, 3, x_8);
x_50 = l_Lake_BuildTrace_mix(x_44, x_40);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_50);
x_51 = x_46;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_77, 0, x_41);
lean_ctor_set(x_77, 1, x_50);
lean_ctor_set(x_77, 2, x_45);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_42);
lean_ctor_set_uint8(x_77, sizeof(void*)*3 + 1, x_43);
x_51 = x_77;
goto block_76;
}
block_76:
{
uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 1;
x_53 = 0;
x_54 = l_Lake_sharedLibExt;
x_55 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_49, x_53, x_54, x_52, x_53, x_9, x_10, x_11, x_12, x_13, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_66; 
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_ctor_get(x_55, 1);
x_66 = !lean_is_exclusive(x_55);
if (x_66 == 0)
{
x_58 = x_55;
x_59 = x_66;
goto block_65;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_55);
x_58 = lean_box(0);
x_59 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
lean_ctor_set(x_61, 2, x_8);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_7);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_61);
x_62 = x_58;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_57);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
x_75 = !lean_is_exclusive(x_55);
if (x_75 == 0)
{
x_69 = x_55;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_80 = lean_ctor_get(x_38, 0);
x_81 = lean_ctor_get(x_38, 1);
x_88 = !lean_is_exclusive(x_38);
if (x_88 == 0)
{
x_82 = x_38;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_38);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_7);
x_18 = l_Lake_buildSharedLib___lam__2(x_1, x_2, x_16, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
x_21 = lean_box(x_6);
x_22 = lean_box(x_8);
x_23 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_3);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_22);
x_24 = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
x_25 = l_Lake_Job_collectArray___redArg(x_9, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
lean_inc_ref(x_19);
x_28 = l_Lake_Job_mapM___redArg(x_10, x_25, x_23, x_26, x_27, x_12, x_13, x_14, x_15, x_16, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_6);
x_20 = lean_unbox(x_8);
x_21 = l_Lake_buildSharedLib___lam__3(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = l_Lake_instDataKindDynlib;
x_19 = lean_box(x_10);
x_20 = lean_box(x_9);
x_21 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_7);
lean_closure_set(x_21, 4, x_8);
lean_closure_set(x_21, 5, x_19);
lean_closure_set(x_21, 6, x_1);
lean_closure_set(x_21, 7, x_20);
lean_closure_set(x_21, 8, x_4);
lean_closure_set(x_21, 9, x_18);
x_22 = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
x_23 = l_Lake_Job_collectArray___redArg(x_3, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 1;
x_26 = l_Lake_Job_bindM___redArg(x_18, x_23, x_21, x_24, x_25, x_11, x_12, x_13, x_14, x_15, x_16);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_9);
x_19 = lean_unbox(x_10);
x_20 = l_Lake_buildSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
return x_20;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
if (x_5 == 0)
{
lean_object* x_64; 
x_64 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
x_17 = x_64;
x_18 = x_12;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_6, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_17 = x_66;
x_18 = x_67;
goto block_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
x_76 = !lean_is_exclusive(x_65);
if (x_76 == 0)
{
x_70 = x_65;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
block_63:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_62; 
x_19 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 13);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 19);
lean_inc_ref(x_21);
lean_dec_ref(x_16);
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 2);
x_62 = !lean_is_exclusive(x_18);
if (x_62 == 0)
{
x_27 = x_18;
x_28 = x_62;
goto block_61;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_30 = l_Array_append___redArg(x_29, x_2);
x_31 = l_Array_append___redArg(x_30, x_3);
x_32 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
x_33 = lean_array_push(x_32, x_19);
x_34 = l_Array_append___redArg(x_31, x_33);
lean_dec_ref(x_33);
x_35 = l_Array_append___redArg(x_34, x_21);
lean_dec_ref(x_21);
x_36 = l_Lake_compileSharedLib(x_4, x_35, x_20, x_22);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_48; 
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
x_39 = x_36;
x_40 = x_48;
goto block_47;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_39 = lean_box(0);
x_40 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_41; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_38);
x_41 = x_27;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_25);
lean_ctor_set(x_46, 2, x_26);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_24);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 1, x_41);
x_42 = x_39;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_60; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
x_51 = x_36;
x_52 = x_60;
goto block_59;
}
else
{
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_box(0);
x_52 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_53; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_50);
x_53 = x_27;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_25);
lean_ctor_set(x_58, 2, x_26);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 1, x_24);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_52 == 0)
{
lean_ctor_set(x_51, 1, x_53);
x_54 = x_51;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanSharedLib___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_80; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_ctor_get(x_14, 2);
x_80 = !lean_is_exclusive(x_14);
if (x_80 == 0)
{
x_21 = x_14;
x_22 = x_80;
goto block_79;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_23 = lean_ctor_get(x_13, 2);
x_24 = lean_box(x_5);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_25 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_24);
lean_closure_set(x_25, 5, x_8);
lean_inc_ref(x_23);
x_26 = l_Lake_BuildTrace_mix(x_19, x_23);
x_68 = l_Lake_Hash_nil;
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_array_get_size(x_3);
x_71 = lean_nat_dec_lt(x_69, x_70);
if (x_71 == 0)
{
x_27 = x_68;
goto block_67;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_70, x_70);
if (x_72 == 0)
{
if (x_71 == 0)
{
x_27 = x_68;
goto block_67;
}
else
{
size_t x_73; size_t x_74; uint64_t x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_70);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_73, x_74, x_68);
x_27 = x_75;
goto block_67;
}
}
else
{
size_t x_76; size_t x_77; uint64_t x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_70);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_76, x_77, x_68);
x_27 = x_78;
goto block_67;
}
}
block_67:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_29 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_30 = lean_array_to_list(x_3);
x_31 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_29, x_31);
lean_dec_ref(x_31);
x_33 = lean_string_append(x_28, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_35 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_36 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*3, x_27);
x_37 = l_Lake_BuildTrace_mix(x_26, x_36);
x_38 = l_Lake_platformTrace;
x_39 = l_Lake_BuildTrace_mix(x_37, x_38);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_39);
x_40 = x_21;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_66, 0, x_16);
lean_ctor_set(x_66, 1, x_39);
lean_ctor_set(x_66, 2, x_20);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_66, sizeof(void*)*3 + 1, x_18);
x_40 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = 0;
x_42 = l_Lake_sharedLibExt;
x_43 = 1;
x_44 = l_Lake_buildArtifactUnlessUpToDate(x_4, x_25, x_41, x_42, x_43, x_41, x_9, x_10, x_11, x_12, x_13, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
x_45 = lean_ctor_get(x_44, 0);
x_46 = lean_ctor_get(x_44, 1);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
x_47 = x_44;
x_48 = x_55;
goto block_54;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
lean_ctor_set(x_50, 2, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_7);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_50);
x_51 = x_47;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_46);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_56 = lean_ctor_get(x_44, 0);
x_57 = lean_ctor_get(x_44, 1);
x_64 = !lean_is_exclusive(x_44);
if (x_64 == 0)
{
x_58 = x_44;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_44);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_7);
x_18 = l_Lake_buildLeanSharedLib___lam__1(x_1, x_2, x_3, x_4, x_16, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_box(x_4);
x_19 = lean_box(x_6);
x_20 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(x_20, 0, x_9);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_19);
x_21 = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
x_22 = l_Lake_Job_collectArray___redArg(x_7, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
lean_inc_ref(x_17);
x_25 = l_Lake_Job_mapM___redArg(x_8, x_22, x_20, x_23, x_24, x_10, x_11, x_12, x_13, x_14, x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_6);
x_19 = l_Lake_buildLeanSharedLib___lam__2(x_1, x_2, x_3, x_17, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = l_Lake_instDataKindDynlib;
x_17 = lean_box(x_8);
x_18 = lean_box(x_7);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_16);
x_20 = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
x_21 = l_Lake_Job_collectArray___redArg(x_3, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 1;
x_24 = l_Lake_Job_bindM___redArg(x_16, x_21, x_19, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_7);
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_65; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_17, 3);
x_21 = lean_ctor_get(x_17, 13);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 2);
x_65 = !lean_is_exclusive(x_18);
if (x_65 == 0)
{
x_27 = x_18;
x_28 = x_65;
goto block_64;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_19);
lean_dec(x_19);
x_30 = l_Array_append___redArg(x_29, x_3);
x_31 = l_Array_append___redArg(x_30, x_4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec_ref(x_33);
x_34 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(x_20);
x_35 = lean_array_push(x_34, x_20);
x_36 = l_Array_append___redArg(x_31, x_35);
lean_dec_ref(x_35);
x_37 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_17);
lean_dec_ref(x_17);
x_38 = l_Array_append___redArg(x_36, x_37);
lean_dec_ref(x_37);
x_39 = l_Lake_compileExe(x_6, x_38, x_21, x_22);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_51; 
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 1);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
x_42 = x_39;
x_43 = x_51;
goto block_50;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_44; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_41);
x_44 = x_27;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_25);
lean_ctor_set(x_49, 2, x_26);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_24);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 1, x_44);
x_45 = x_42;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_63; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
x_54 = x_39;
x_55 = x_63;
goto block_62;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_54 = lean_box(0);
x_55 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_56; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_53);
x_56 = x_27;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_25);
lean_ctor_set(x_61, 2, x_26);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_61, sizeof(void*)*3 + 1, x_24);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_55 == 0)
{
lean_ctor_set(x_54, 1, x_56);
x_57 = x_54;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
x_66 = lean_ctor_get(x_14, 0);
x_67 = lean_ctor_get(x_14, 1);
x_74 = !lean_is_exclusive(x_14);
if (x_74 == 0)
{
x_68 = x_14;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_14);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanExe___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_77; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_77 = !lean_is_exclusive(x_12);
if (x_77 == 0)
{
x_19 = x_12;
x_20 = x_77;
goto block_76;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_21 = lean_ctor_get(x_11, 2);
x_22 = lean_box(x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_23 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(x_23, 0, x_6);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_22);
lean_closure_set(x_23, 5, x_5);
lean_inc_ref(x_21);
x_24 = l_Lake_BuildTrace_mix(x_17, x_21);
x_65 = l_Lake_Hash_nil;
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_array_get_size(x_3);
x_68 = lean_nat_dec_lt(x_66, x_67);
if (x_68 == 0)
{
x_25 = x_65;
goto block_64;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
if (x_68 == 0)
{
x_25 = x_65;
goto block_64;
}
else
{
size_t x_70; size_t x_71; uint64_t x_72; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_67);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_70, x_71, x_65);
x_25 = x_72;
goto block_64;
}
}
else
{
size_t x_73; size_t x_74; uint64_t x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_67);
x_75 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_73, x_74, x_65);
x_25 = x_75;
goto block_64;
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_27 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_28 = lean_array_to_list(x_3);
x_29 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_26, x_30);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l_Lake_platformTrace___closed__2));
x_33 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_34 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_25);
x_35 = l_Lake_BuildTrace_mix(x_24, x_34);
x_36 = l_Lake_platformTrace;
x_37 = l_Lake_BuildTrace_mix(x_35, x_36);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_37);
x_38 = x_19;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_37);
lean_ctor_set(x_63, 2, x_18);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_63, sizeof(void*)*3 + 1, x_16);
x_38 = x_63;
goto block_62;
}
block_62:
{
uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_39 = 0;
x_40 = l_System_FilePath_exeExtension;
x_41 = 1;
x_42 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_23, x_39, x_40, x_41, x_41, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_52; 
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 1);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
x_45 = x_42;
x_46 = x_52;
goto block_51;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_47);
lean_dec(x_43);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_47);
x_48 = x_45;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_44);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
x_55 = x_42;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lake_buildLeanExe___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_4);
x_18 = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
x_19 = l_Lake_Job_collectArray___redArg(x_5, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
lean_inc_ref(x_15);
x_22 = l_Lake_Job_mapM___redArg(x_6, x_19, x_17, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_Lake_buildLeanExe___lam__2(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_box(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_1);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_14);
x_17 = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
x_18 = l_Lake_Job_collectArray___redArg(x_2, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 1;
x_21 = l_Lake_Job_bindM___redArg(x_14, x_18, x_16, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadWorkspaceJobM = _init_l_Lake_instMonadWorkspaceJobM();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_buildO___lam__2___boxed__const__1 = _init_l_Lake_buildO___lam__2___boxed__const__1();
lean_mark_persistent(l_Lake_buildO___lam__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Common(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Common(builtin);
}
#ifdef __cplusplus
}
#endif
