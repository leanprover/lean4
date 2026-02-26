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
static lean_once_cell_t l_Lake_platformTrace___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__2;
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
static lean_once_cell_t l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0;
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
static lean_once_cell_t l_Lake_BuildMetadata_ofStub___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_ofStub___closed__0;
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
static lean_once_cell_t l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "log: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "outputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
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
uint8_t l_Array_isEmpty___redArg(lean_object*);
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
static const lean_string_object l_Lake_buildAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nobuild"};
static const lean_object* l_Lake_buildAction___redArg___closed__0 = (const lean_object*)&l_Lake_buildAction___redArg___closed__0_value;
static const lean_string_object l_Lake_buildAction___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "target is out-of-date and needs to be rebuilt"};
static const lean_object* l_Lake_buildAction___redArg___closed__1 = (const lean_object*)&l_Lake_buildAction___redArg___closed__1_value;
static const lean_ctor_object l_Lake_buildAction___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_buildAction___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_buildAction___redArg___closed__2 = (const lean_object*)&l_Lake_buildAction___redArg___closed__2_value;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
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
uint8_t l_System_FilePath_pathExists(lean_object*);
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
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__0_value;
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "' found in package artifact cache, but some output(s) have issues: "};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__1_value;
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output `"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1_value;
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object**);
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
static lean_once_cell_t l_Lake_inputDir___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_inputDir___lam__1___closed__0;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
static lean_once_cell_t l_Lake_buildLeanO___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanO___lam__0___closed__2;
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
static const lean_string_object l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0 = (const lean_object*)&l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0_value;
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
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
lean_object* x_1; uint8_t x_2; 
x_1 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__0, &l_Lake_instMonadWorkspaceJobM___closed__0_once, _init_l_Lake_instMonadWorkspaceJobM___closed__0);
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_inc(x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
lean_inc_ref(x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_5);
x_15 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_16, 0, x_7);
lean_inc_ref(x_15);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_11);
lean_inc_ref(x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__16, &l_Lake_instMonadWorkspaceJobM___closed__16_once, _init_l_Lake_instMonadWorkspaceJobM___closed__16);
lean_inc_ref(x_1);
x_21 = l_ReaderT_instAlternativeOfMonad___redArg(x_20, x_1);
x_22 = l_ReaderT_instMonad___redArg(x_1);
lean_inc_ref(x_22);
x_23 = l_ReaderT_instAlternativeOfMonad___redArg(x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__20, &l_Lake_instMonadWorkspaceJobM___closed__20_once, _init_l_Lake_instMonadWorkspaceJobM___closed__20);
lean_inc_ref(x_19);
x_27 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_26, x_19);
x_28 = l_ReaderT_instMonad___redArg(x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_27, x_19);
x_32 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, lean_box(0));
lean_closure_set(x_32, 3, lean_box(0));
lean_closure_set(x_32, 4, x_31);
lean_inc_ref(x_25);
x_33 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_32, x_25);
lean_inc_ref(x_30);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_30);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_ReaderT_instMonad___redArg(x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
lean_dec_ref(x_38);
x_40 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_33, x_25);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_40);
lean_inc_ref(x_36);
x_42 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_41, x_36);
x_43 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_42, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_44, 0, lean_box(0));
lean_closure_set(x_44, 1, x_43);
lean_inc_ref(x_39);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_39);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc_ref(x_47);
x_48 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_44, x_47);
lean_inc_ref(x_47);
x_49 = l_Lake_EquipT_instFunctor___redArg(x_47);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
lean_dec_ref(x_51);
x_54 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_48, x_47);
x_55 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, lean_box(0));
lean_closure_set(x_55, 2, lean_box(0));
lean_closure_set(x_55, 3, x_54);
lean_inc_ref(x_49);
x_56 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_55, x_49);
x_57 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_56, x_49);
x_58 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_57);
lean_inc_ref(x_53);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_53);
lean_ctor_set(x_37, 1, x_60);
lean_ctor_set(x_37, 0, x_59);
x_61 = l_Lake_EquipT_instFunctor___redArg(x_37);
x_62 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_58, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_37, 0);
lean_inc(x_63);
lean_dec(x_37);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
lean_dec_ref(x_63);
x_65 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_48, x_47);
x_66 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_66, 0, lean_box(0));
lean_closure_set(x_66, 1, lean_box(0));
lean_closure_set(x_66, 2, lean_box(0));
lean_closure_set(x_66, 3, x_65);
lean_inc_ref(x_49);
x_67 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_66, x_49);
x_68 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_67, x_49);
x_69 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_69, 0, lean_box(0));
lean_closure_set(x_69, 1, x_68);
lean_inc_ref(x_64);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_70, 0, x_64);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lake_EquipT_instFunctor___redArg(x_72);
x_74 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_69, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_75 = lean_ctor_get(x_1, 1);
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_3);
lean_inc(x_75);
lean_inc(x_77);
x_78 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_75);
lean_inc(x_75);
lean_inc(x_77);
x_79 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_79, 0, x_77);
lean_closure_set(x_79, 1, x_75);
lean_inc_ref(x_78);
lean_inc(x_77);
x_80 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_80, 0, x_77);
lean_closure_set(x_80, 1, x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
x_81 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_81, 0, x_76);
lean_closure_set(x_81, 1, x_77);
lean_closure_set(x_81, 2, x_75);
x_82 = l_Lake_EStateT_instFunctor___redArg(x_76);
x_83 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_83, 0, x_77);
lean_inc_ref(x_82);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_84);
lean_inc_ref(x_82);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_85, 0, x_82);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_86, 0, x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__16, &l_Lake_instMonadWorkspaceJobM___closed__16_once, _init_l_Lake_instMonadWorkspaceJobM___closed__16);
lean_inc_ref(x_1);
x_89 = l_ReaderT_instAlternativeOfMonad___redArg(x_88, x_1);
x_90 = l_ReaderT_instMonad___redArg(x_1);
lean_inc_ref(x_90);
x_91 = l_ReaderT_instAlternativeOfMonad___redArg(x_89, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_92);
lean_dec_ref(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
lean_dec_ref(x_92);
x_94 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__20, &l_Lake_instMonadWorkspaceJobM___closed__20_once, _init_l_Lake_instMonadWorkspaceJobM___closed__20);
lean_inc_ref(x_87);
x_95 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_94, x_87);
x_96 = l_ReaderT_instMonad___redArg(x_90);
x_97 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_98);
lean_dec_ref(x_97);
x_99 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_95, x_87);
x_100 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_100, 0, lean_box(0));
lean_closure_set(x_100, 1, lean_box(0));
lean_closure_set(x_100, 2, lean_box(0));
lean_closure_set(x_100, 3, lean_box(0));
lean_closure_set(x_100, 4, x_99);
lean_inc_ref(x_93);
x_101 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_100, x_93);
lean_inc_ref(x_98);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_102, 0, x_98);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_103, 0, x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_ReaderT_instMonad___redArg(x_96);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
lean_dec_ref(x_106);
x_108 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_101, x_93);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_109, 0, lean_box(0));
lean_closure_set(x_109, 1, x_108);
lean_inc_ref(x_104);
x_110 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_109, x_104);
x_111 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_110, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_112, 0, lean_box(0));
lean_closure_set(x_112, 1, x_111);
lean_inc_ref(x_107);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_107);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_inc_ref(x_115);
x_116 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_112, x_115);
lean_inc_ref(x_115);
x_117 = l_Lake_EquipT_instFunctor___redArg(x_115);
x_118 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
lean_dec_ref(x_118);
x_121 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_116, x_115);
x_122 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_122, 0, lean_box(0));
lean_closure_set(x_122, 1, lean_box(0));
lean_closure_set(x_122, 2, lean_box(0));
lean_closure_set(x_122, 3, x_121);
lean_inc_ref(x_117);
x_123 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_122, x_117);
x_124 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_123, x_117);
x_125 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_125, 0, lean_box(0));
lean_closure_set(x_125, 1, x_124);
lean_inc_ref(x_120);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_126, 0, x_120);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lake_EquipT_instFunctor___redArg(x_128);
x_130 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_125, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_131 = lean_ctor_get(x_1, 0);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_1);
x_133 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
lean_inc(x_132);
lean_inc(x_134);
x_136 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_136, 0, x_134);
lean_closure_set(x_136, 1, x_132);
lean_inc(x_132);
lean_inc(x_134);
x_137 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_137, 0, x_134);
lean_closure_set(x_137, 1, x_132);
lean_inc_ref(x_136);
lean_inc(x_134);
x_138 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_138, 0, x_134);
lean_closure_set(x_138, 1, x_136);
lean_inc(x_134);
lean_inc_ref(x_133);
x_139 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_139, 0, x_133);
lean_closure_set(x_139, 1, x_134);
lean_closure_set(x_139, 2, x_132);
x_140 = l_Lake_EStateT_instFunctor___redArg(x_133);
x_141 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_141, 0, x_134);
lean_inc_ref(x_140);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set(x_142, 4, x_137);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_136);
lean_inc_ref(x_140);
x_144 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_144, 0, x_140);
x_145 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_145, 0, x_140);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__16, &l_Lake_instMonadWorkspaceJobM___closed__16_once, _init_l_Lake_instMonadWorkspaceJobM___closed__16);
lean_inc_ref(x_143);
x_148 = l_ReaderT_instAlternativeOfMonad___redArg(x_147, x_143);
x_149 = l_ReaderT_instMonad___redArg(x_143);
lean_inc_ref(x_149);
x_150 = l_ReaderT_instAlternativeOfMonad___redArg(x_148, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc_ref(x_151);
lean_dec_ref(x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_152);
lean_dec_ref(x_151);
x_153 = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__20, &l_Lake_instMonadWorkspaceJobM___closed__20_once, _init_l_Lake_instMonadWorkspaceJobM___closed__20);
lean_inc_ref(x_146);
x_154 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_153, x_146);
x_155 = l_ReaderT_instMonad___redArg(x_149);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_157);
lean_dec_ref(x_156);
x_158 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_154, x_146);
x_159 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_159, 0, lean_box(0));
lean_closure_set(x_159, 1, lean_box(0));
lean_closure_set(x_159, 2, lean_box(0));
lean_closure_set(x_159, 3, lean_box(0));
lean_closure_set(x_159, 4, x_158);
lean_inc_ref(x_152);
x_160 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_159, x_152);
lean_inc_ref(x_157);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_161, 0, x_157);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_162, 0, x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_ReaderT_instMonad___redArg(x_155);
x_165 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_166);
lean_dec_ref(x_165);
x_167 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_160, x_152);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_168, 0, lean_box(0));
lean_closure_set(x_168, 1, x_167);
lean_inc_ref(x_163);
x_169 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_168, x_163);
x_170 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_169, x_163);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_171, 0, lean_box(0));
lean_closure_set(x_171, 1, x_170);
lean_inc_ref(x_166);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_172, 0, x_166);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_inc_ref(x_174);
x_175 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_171, x_174);
lean_inc_ref(x_174);
x_176 = l_Lake_EquipT_instFunctor___redArg(x_174);
x_177 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_177);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_178 = x_164;
} else {
 lean_dec_ref(x_164);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_179);
lean_dec_ref(x_177);
x_180 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_175, x_174);
x_181 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_181, 0, lean_box(0));
lean_closure_set(x_181, 1, lean_box(0));
lean_closure_set(x_181, 2, lean_box(0));
lean_closure_set(x_181, 3, x_180);
lean_inc_ref(x_176);
x_182 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_181, x_176);
x_183 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_182, x_176);
x_184 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_184, 0, lean_box(0));
lean_closure_set(x_184, 1, x_183);
lean_inc_ref(x_179);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_185, 0, x_179);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_186, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_178;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lake_EquipT_instFunctor___redArg(x_187);
x_189 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_184, x_188);
return x_189;
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
static lean_object* _init_l_Lake_platformTrace___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
x_3 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_platformTrace;
x_6 = lean_box(0);
x_7 = l_Lake_BuildTrace_mix(x_4, x_5);
lean_ctor_set(x_1, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_dec(x_1);
x_14 = l_Lake_platformTrace;
x_15 = lean_box(0);
x_16 = l_Lake_BuildTrace_mix(x_12, x_14);
x_17 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lake_platformTrace;
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_6);
x_19 = l_Lake_platformTrace;
x_20 = lean_box(0);
x_21 = l_Lake_BuildTrace_mix(x_17, x_19);
x_22 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = l_Lake_BuildTrace_mix(x_5, x_6);
lean_ctor_set(x_2, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = l_Lake_BuildTrace_mix(x_13, x_15);
x_18 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_5);
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_6);
x_19 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_5);
x_20 = lean_box(0);
x_21 = l_Lake_BuildTrace_mix(x_17, x_19);
x_22 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
x_9 = lean_apply_1(x_2, x_3);
x_10 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_11 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_12 = lean_string_append(x_4, x_11);
x_13 = lean_apply_1(x_1, x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_16 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox_uint64(x_9);
lean_dec_ref(x_9);
lean_ctor_set_uint64(x_16, sizeof(void*)*3, x_17);
x_18 = lean_box(0);
x_19 = l_Lake_BuildTrace_mix(x_8, x_16);
lean_ctor_set(x_5, 1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_3);
x_26 = lean_apply_1(x_2, x_3);
x_27 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_28 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_29 = lean_string_append(x_4, x_28);
x_30 = lean_apply_1(x_1, x_3);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_33 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_unbox_uint64(x_26);
lean_dec_ref(x_26);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_34);
x_35 = lean_box(0);
x_36 = l_Lake_BuildTrace_mix(x_24, x_33);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_23);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_15 = lean_apply_1(x_3, x_4);
x_16 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_17 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_apply_1(x_2, x_4);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_22 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_unbox_uint64(x_15);
lean_dec_ref(x_15);
lean_ctor_set_uint64(x_22, sizeof(void*)*3, x_23);
x_24 = lean_box(0);
x_25 = l_Lake_BuildTrace_mix(x_14, x_22);
lean_ctor_set(x_11, 1, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_29 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_27);
lean_dec(x_11);
lean_inc(x_4);
x_32 = lean_apply_1(x_3, x_4);
x_33 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_34 = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
x_35 = lean_string_append(x_5, x_34);
x_36 = lean_apply_1(x_2, x_4);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_38 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_39 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_unbox_uint64(x_32);
lean_dec_ref(x_32);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_40);
x_41 = lean_box(0);
x_42 = l_Lake_BuildTrace_mix(x_30, x_39);
x_43 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_28);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_29);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
static lean_object* _init_l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_obj_once(&l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0, &l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0_once, _init_l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0);
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
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
static lean_object* _init_l_Lake_BuildMetadata_ofStub___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_obj_once(&l_Lake_BuildMetadata_ofStub___closed__0, &l_Lake_BuildMetadata_ofStub___closed__0_once, _init_l_Lake_BuildMetadata_ofStub___closed__0);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
lean_object* x_3; uint8_t x_4; 
x_3 = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
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
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
uint8_t x_18; 
lean_dec_ref(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_array_fget(x_11, x_23);
lean_dec_ref(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_fget(x_11, x_27);
lean_dec_ref(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
uint8_t x_8; 
lean_dec_ref(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint64_t x_44; lean_object* x_45; lean_object* x_46; uint64_t x_65; lean_object* x_66; uint64_t x_69; lean_object* x_70; uint64_t x_89; uint64_t x_92; lean_object* x_111; lean_object* x_112; 
x_111 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
x_112 = l_Lake_JsonObject_getJson_x3f(x_1, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
x_114 = l_Lake_JsonObject_getJson_x3f(x_1, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = l_Lean_Json_getStr_x3f(x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_121);
return x_117;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
x_123 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_117);
if (x_126 == 0)
{
lean_ctor_set_tag(x_117, 0);
return x_117;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
lean_dec(x_117);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
lean_dec_ref(x_117);
x_130 = l_Lake_Hash_ofDecimal_x3f(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return x_131;
}
else
{
lean_object* x_132; uint64_t x_133; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec_ref(x_130);
x_133 = lean_unbox_uint64(x_132);
lean_dec(x_132);
x_92 = x_133;
goto block_110;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_112);
x_134 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
x_135 = l_Lake_JsonObject_getJson_x3f(x_1, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = l_Lake_Hash_fromJson_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_142);
return x_138;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
lean_dec(x_138);
x_144 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
x_145 = lean_string_append(x_144, x_143);
lean_dec(x_143);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_138);
if (x_147 == 0)
{
lean_ctor_set_tag(x_138, 0);
return x_138;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
lean_dec(x_138);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
else
{
lean_object* x_150; uint64_t x_151; 
x_150 = lean_ctor_get(x_138, 0);
lean_inc(x_150);
lean_dec_ref(x_138);
x_151 = lean_unbox_uint64(x_150);
lean_dec(x_150);
x_92 = x_151;
goto block_110;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set_uint64(x_7, sizeof(void*)*3, x_2);
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
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
goto block_9;
}
block_38:
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
x_21 = l_Lake_JsonObject_getJson_x3f(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
x_10 = x_16;
x_11 = x_19;
x_12 = x_17;
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
uint8_t x_24; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_ctor_set_tag(x_23, 0);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec_ref(x_23);
if (lean_obj_tag(x_35) == 0)
{
x_10 = x_16;
x_11 = x_19;
x_12 = x_17;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_2 = x_16;
x_3 = x_19;
x_4 = x_17;
x_5 = x_18;
x_6 = x_37;
goto block_9;
}
}
}
}
}
block_43:
{
lean_object* x_42; 
x_42 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
goto block_38;
}
block_64:
{
lean_object* x_47; lean_object* x_48; 
x_47 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
x_48 = l_Lake_JsonObject_getJson_x3f(x_1, x_47);
if (lean_obj_tag(x_48) == 0)
{
x_39 = x_44;
x_40 = x_46;
x_41 = x_45;
goto block_43;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec_ref(x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_59; 
lean_dec(x_46);
lean_dec_ref(x_45);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
lean_ctor_set_tag(x_50, 0);
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
if (lean_obj_tag(x_62) == 0)
{
x_39 = x_44;
x_40 = x_46;
x_41 = x_45;
goto block_43;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_16 = x_44;
x_17 = x_46;
x_18 = x_45;
x_19 = x_63;
goto block_38;
}
}
}
}
}
block_68:
{
lean_object* x_67; 
x_67 = lean_box(0);
x_44 = x_65;
x_45 = x_66;
x_46 = x_67;
goto block_64;
}
block_88:
{
lean_object* x_71; lean_object* x_72; 
x_71 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
x_72 = l_Lake_JsonObject_getJson_x3f(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
x_65 = x_69;
x_66 = x_70;
goto block_68;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec_ref(x_70);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_78);
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_83; 
lean_dec_ref(x_70);
x_83 = !lean_is_exclusive(x_74);
if (x_83 == 0)
{
lean_ctor_set_tag(x_74, 0);
return x_74;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_74, 0);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
lean_dec_ref(x_74);
if (lean_obj_tag(x_86) == 0)
{
x_65 = x_69;
x_66 = x_70;
goto block_68;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_44 = x_69;
x_45 = x_70;
x_46 = x_87;
goto block_64;
}
}
}
}
}
block_91:
{
lean_object* x_90; 
x_90 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4);
x_69 = x_89;
x_70 = x_90;
goto block_88;
}
block_110:
{
lean_object* x_93; lean_object* x_94; 
x_93 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
x_94 = l_Lake_JsonObject_getJson_x3f(x_1, x_93);
if (lean_obj_tag(x_94) == 0)
{
x_89 = x_92;
goto block_91;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_dec(x_96);
x_102 = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
lean_ctor_set_tag(x_96, 0);
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
lean_dec(x_96);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
lean_dec_ref(x_96);
if (lean_obj_tag(x_108) == 0)
{
x_89 = x_92;
goto block_91;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_69 = x_92;
x_70 = x_109;
goto block_88;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = l_Lake_BuildMetadata_ofStub(x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_18 = l_Lake_BuildMetadata_ofStub(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
case 5:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = l_Lake_BuildMetadata_fromJsonObject_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_28 = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
x_29 = l_Lake_JsonObject_getJson_x3f(x_20, x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 3)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
x_34 = lean_string_dec_eq(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_free_object(x_30);
goto block_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
x_35 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
x_36 = lean_string_append(x_35, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
x_38 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_23);
x_40 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
x_41 = lean_string_append(x_40, x_22);
lean_dec(x_22);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_30);
goto block_27;
}
}
else
{
lean_dec(x_29);
goto block_27;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
x_25 = lean_string_append(x_24, x_22);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
return x_21;
}
}
default: 
{
lean_object* x_43; 
x_43 = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return x_43;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lake_BuildMetadata_fromJson_x3f(x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_Lake_BuildMetadata_ofStub___closed__0, &l_Lake_BuildMetadata_ofStub___closed__0_once, _init_l_Lake_BuildMetadata_ofStub___closed__0);
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
lean_object* x_6; lean_object* x_7; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_17 = l_Array_isEmpty___redArg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
x_19 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lake_Hash_hex(x_16);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
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
x_3 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4);
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
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_ctor_set_tag(x_19, 2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
return x_25;
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
lean_object* x_26; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec_ref(x_4);
if (lean_obj_tag(x_26) == 11)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = ((lean_object*)(l_Lake_readTraceFile___closed__0));
x_30 = lean_string_append(x_1, x_29);
x_31 = lean_io_error_to_string(x_26);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_2);
x_36 = lean_array_push(x_2, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = 0;
x_14 = lean_unbox(x_12);
lean_dec(x_12);
x_15 = l_Lake_instDecidableEqOutputStatus(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = 0;
x_23 = lean_unbox(x_20);
lean_dec(x_20);
x_24 = l_Lake_instDecidableEqOutputStatus(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
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
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lake_instDecidableEqOutputStatus(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = 0;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_array_uget_borrowed(x_1, x_2);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_array_push(x_9, x_10);
lean_ctor_set(x_5, 0, x_12);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_dec(x_5);
x_21 = lean_array_uget_borrowed(x_1, x_2);
x_22 = lean_box(0);
lean_inc(x_21);
x_23 = lean_array_push(x_16, x_21);
x_24 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_18);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_4 = x_22;
x_5 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
return x_28;
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get_uint64(x_15, sizeof(void*)*3);
x_17 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_18 = lean_box_uint64(x_16);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_18);
x_19 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_27 = 0;
x_28 = lean_unbox(x_20);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_32 = 1;
x_33 = l_Lake_JobAction_merge(x_31, x_32);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_33);
x_34 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec_ref(x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_23 = x_35;
x_24 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_20);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_21, 1);
x_44 = lean_ctor_get(x_21, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_40);
lean_dec(x_21);
x_45 = 1;
x_46 = l_Lake_JobAction_merge(x_41, x_45);
x_47 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 1, x_42);
x_48 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_47);
lean_dec_ref(x_17);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_23 = x_49;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_22);
lean_dec(x_20);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_dec_ref(x_17);
x_23 = x_21;
x_24 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_25; 
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_dec(x_5);
x_55 = lean_ctor_get_uint64(x_54, sizeof(void*)*3);
x_56 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_56);
lean_dec_ref(x_54);
x_57 = lean_box_uint64(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_58, x_6, x_11, x_12);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_67 = 0;
x_68 = lean_unbox(x_60);
x_69 = l_Lake_instDecidableEqOutputStatus(x_68, x_67);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get_uint8(x_61, sizeof(void*)*3);
x_72 = lean_ctor_get_uint8(x_61, sizeof(void*)*3 + 1);
x_73 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_61, 2);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
x_76 = 1;
x_77 = l_Lake_JobAction_merge(x_71, x_76);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 3, 2);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 1, x_72);
x_79 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_56, x_7, x_8, x_9, x_10, x_11, x_78);
lean_dec_ref(x_56);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_63 = x_80;
x_64 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_62);
lean_dec(x_60);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_dec_ref(x_56);
x_63 = x_61;
x_64 = lean_box(0);
goto block_66;
}
block_66:
{
lean_object* x_65; 
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_11, 0);
x_86 = lean_ctor_get_uint8(x_85, sizeof(void*)*2);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_12);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_90 == 0)
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_91 = 0;
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_12);
return x_93;
}
else
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_94 = 1;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_12);
return x_96;
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = 0;
x_18 = lean_unbox(x_16);
lean_dec(x_16);
x_19 = l_Lake_instDecidableEqOutputStatus(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = 0;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
x_28 = l_Lake_instDecidableEqOutputStatus(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lake_instDecidableEqOutputStatus(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = 0;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get_uint64(x_26, sizeof(void*)*3);
x_28 = lean_ctor_get(x_26, 2);
x_29 = lean_ctor_get_uint8(x_26, sizeof(void*)*3 + 8);
x_30 = lean_uint64_dec_eq(x_27, x_1);
if (x_30 == 0)
{
x_5 = x_3;
x_6 = lean_box(0);
goto block_25;
}
else
{
if (x_29 == 0)
{
goto block_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_array_get_size(x_28);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
if (x_80 == 0)
{
goto block_77;
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
uint8_t x_82; uint8_t x_83; uint8_t x_84; 
x_82 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_83 = 2;
x_84 = l_Lake_JobAction_merge(x_82, x_83);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_84);
x_31 = x_3;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_3, 0);
x_86 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_87 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_88 = lean_ctor_get(x_3, 1);
x_89 = lean_ctor_get(x_3, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_85);
lean_dec(x_3);
x_90 = 2;
x_91 = l_Lake_JobAction_merge(x_86, x_90);
x_92 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*3 + 1, x_87);
x_31 = x_92;
x_32 = lean_box(0);
goto block_35;
}
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
block_42:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_31 = x_37;
x_32 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_77:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_45 = 1;
x_46 = l_Lake_JobAction_merge(x_44, x_45);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_28);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
x_31 = x_3;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_49 == 0)
{
x_31 = x_3;
x_32 = lean_box(0);
goto block_35;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_28, x_52, x_53, x_50, x_3);
x_36 = x_54;
goto block_42;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_48);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_28, x_55, x_56, x_50, x_3);
x_36 = x_57;
goto block_42;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_58 = lean_ctor_get(x_3, 0);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_60 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_61 = lean_ctor_get(x_3, 1);
x_62 = lean_ctor_get(x_3, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_58);
lean_dec(x_3);
x_63 = 1;
x_64 = l_Lake_JobAction_merge(x_59, x_63);
x_65 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3 + 1, x_60);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_array_get_size(x_28);
x_68 = lean_nat_dec_lt(x_66, x_67);
if (x_68 == 0)
{
x_31 = x_65;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_box(0);
x_70 = lean_nat_dec_le(x_67, x_67);
if (x_70 == 0)
{
if (x_68 == 0)
{
x_31 = x_65;
x_32 = lean_box(0);
goto block_35;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_67);
x_73 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_28, x_71, x_72, x_69, x_65);
x_36 = x_73;
goto block_42;
}
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_67);
x_76 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_28, x_74, x_75, x_69, x_65);
x_36 = x_76;
goto block_42;
}
}
}
}
}
else
{
x_5 = x_3;
x_6 = lean_box(0);
goto block_25;
}
block_25:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_9 = 2;
x_10 = l_Lake_JobAction_merge(x_8, x_9);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_10);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_dec(x_5);
x_19 = 2;
x_20 = l_Lake_JobAction_merge(x_15, x_19);
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_16);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_3);
x_17 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 2);
x_23 = l_Lake_JobAction_merge(x_21, x_5);
x_24 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_3);
x_25 = l_System_FilePath_addExtension(x_3, x_24);
if (x_22 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_io_mono_ms_now();
lean_inc_ref(x_20);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
x_27 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*3);
x_40 = lean_ctor_get_uint8(x_36, sizeof(void*)*3 + 1);
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 2);
x_43 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_44 = lean_array_get_size(x_38);
x_45 = l_Array_extract___redArg(x_38, x_43, x_44);
lean_inc(x_37);
x_46 = lean_apply_1(x_1, x_37);
x_47 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_46, x_45);
x_48 = l_Lake_BuildMetadata_writeFile(x_3, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_48);
x_49 = l_Lake_removeFileIfExists(x_25);
lean_dec_ref(x_25);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_inc(x_37);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_52);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_27);
x_53 = l_Lake_buildAction___redArg___lam__0(x_26, x_49, x_36);
lean_dec_ref(x_49);
lean_dec(x_26);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_37);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_37);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
x_58 = lean_box(0);
lean_inc(x_37);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_27);
x_60 = l_Lake_buildAction___redArg___lam__0(x_26, x_59, x_36);
lean_dec_ref(x_59);
lean_dec(x_26);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_38);
lean_free_object(x_27);
lean_dec(x_37);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_36, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_36, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_36, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
lean_dec_ref(x_49);
x_69 = lean_io_error_to_string(x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_push(x_38, x_71);
lean_ctor_set(x_36, 0, x_72);
x_28 = x_44;
x_29 = x_36;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_36);
x_73 = lean_ctor_get(x_49, 0);
lean_inc(x_73);
lean_dec_ref(x_49);
x_74 = lean_io_error_to_string(x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_push(x_38, x_76);
x_78 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_41);
lean_ctor_set(x_78, 2, x_42);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_39);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 1, x_40);
x_28 = x_44;
x_29 = x_78;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
uint8_t x_79; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_38);
lean_free_object(x_27);
lean_dec(x_37);
lean_dec_ref(x_25);
x_79 = !lean_is_exclusive(x_36);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_36, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_36, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_36, 0);
lean_dec(x_82);
x_83 = lean_ctor_get(x_48, 0);
lean_inc(x_83);
lean_dec_ref(x_48);
x_84 = lean_io_error_to_string(x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_array_push(x_38, x_86);
lean_ctor_set(x_36, 0, x_87);
x_28 = x_44;
x_29 = x_36;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_36);
x_88 = lean_ctor_get(x_48, 0);
lean_inc(x_88);
lean_dec_ref(x_48);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_push(x_38, x_91);
x_93 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_41);
lean_ctor_set(x_93, 2, x_42);
lean_ctor_set_uint8(x_93, sizeof(void*)*3, x_39);
lean_ctor_set_uint8(x_93, sizeof(void*)*3 + 1, x_40);
x_28 = x_44;
x_29 = x_93;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_ctor_get(x_27, 1);
x_95 = lean_ctor_get(x_27, 0);
lean_inc(x_94);
lean_inc(x_95);
lean_dec(x_27);
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get_uint8(x_94, sizeof(void*)*3);
x_98 = lean_ctor_get_uint8(x_94, sizeof(void*)*3 + 1);
x_99 = lean_ctor_get(x_94, 1);
x_100 = lean_ctor_get(x_94, 2);
x_101 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_102 = lean_array_get_size(x_96);
x_103 = l_Array_extract___redArg(x_96, x_101, x_102);
lean_inc(x_95);
x_104 = lean_apply_1(x_1, x_95);
x_105 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_104, x_103);
x_106 = l_Lake_BuildMetadata_writeFile(x_3, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec_ref(x_106);
x_107 = l_Lake_removeFileIfExists(x_25);
lean_dec_ref(x_25);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_108 = x_107;
} else {
 lean_dec_ref(x_107);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
lean_inc(x_95);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_108;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lake_buildAction___redArg___lam__0(x_26, x_111, x_94);
lean_dec_ref(x_111);
lean_dec(x_26);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_95);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc_ref(x_96);
lean_dec(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 x_116 = x_94;
} else {
 lean_dec_ref(x_94);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
lean_dec_ref(x_107);
x_118 = lean_io_error_to_string(x_117);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_array_push(x_96, x_120);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 3, 2);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_99);
lean_ctor_set(x_122, 2, x_100);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_97);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 1, x_98);
x_28 = x_102;
x_29 = x_122;
x_30 = lean_box(0);
goto block_34;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_25);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 x_123 = x_94;
} else {
 lean_dec_ref(x_94);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_106, 0);
lean_inc(x_124);
lean_dec_ref(x_106);
x_125 = lean_io_error_to_string(x_124);
x_126 = 3;
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = lean_array_push(x_96, x_127);
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(0, 3, 2);
} else {
 x_129 = x_123;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_99);
lean_ctor_set(x_129, 2, x_100);
lean_ctor_set_uint8(x_129, sizeof(void*)*3, x_97);
lean_ctor_set_uint8(x_129, sizeof(void*)*3 + 1, x_98);
x_28 = x_102;
x_29 = x_129;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_27, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_27, 1);
lean_inc(x_131);
lean_dec_ref(x_27);
x_28 = x_130;
x_29 = x_131;
x_30 = lean_box(0);
goto block_34;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_box(0);
x_32 = l_Lake_buildAction___redArg___lam__0(x_26, x_31, x_29);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_13 = x_28;
x_14 = x_33;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_132 = lean_box(0);
x_133 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_134 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_132, x_133);
x_135 = l_Lake_BuildMetadata_writeFile(x_25, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_135);
x_136 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_137 = lean_array_get_size(x_20);
x_138 = lean_array_push(x_20, x_136);
lean_ctor_set(x_11, 0, x_138);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_22);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_11);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
lean_dec_ref(x_135);
x_141 = lean_io_error_to_string(x_140);
x_142 = 3;
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_142);
x_144 = lean_array_get_size(x_20);
x_145 = lean_array_push(x_20, x_143);
lean_ctor_set(x_11, 0, x_145);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_22);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_11);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_10, 0);
x_148 = lean_ctor_get(x_11, 0);
x_149 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_150 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_151 = lean_ctor_get(x_11, 1);
x_152 = lean_ctor_get(x_11, 2);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_148);
lean_dec(x_11);
x_153 = lean_ctor_get_uint8(x_147, sizeof(void*)*2 + 2);
x_154 = l_Lake_JobAction_merge(x_149, x_5);
x_155 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_3);
x_156 = l_System_FilePath_addExtension(x_3, x_155);
if (x_153 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_io_mono_ms_now();
lean_inc_ref(x_148);
x_158 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_158, 0, x_148);
lean_ctor_set(x_158, 1, x_151);
lean_ctor_set(x_158, 2, x_152);
lean_ctor_set_uint8(x_158, sizeof(void*)*3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*3 + 1, x_150);
x_159 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_158, lean_box(0));
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_159, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_169 = x_159;
} else {
 lean_dec_ref(x_159);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_167, 0);
x_171 = lean_ctor_get_uint8(x_167, sizeof(void*)*3);
x_172 = lean_ctor_get_uint8(x_167, sizeof(void*)*3 + 1);
x_173 = lean_ctor_get(x_167, 1);
x_174 = lean_ctor_get(x_167, 2);
x_175 = lean_array_get_size(x_148);
lean_dec_ref(x_148);
x_176 = lean_array_get_size(x_170);
x_177 = l_Array_extract___redArg(x_170, x_175, x_176);
lean_inc(x_168);
x_178 = lean_apply_1(x_1, x_168);
x_179 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_178, x_177);
x_180 = l_Lake_BuildMetadata_writeFile(x_3, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_dec_ref(x_180);
x_181 = l_Lake_removeFileIfExists(x_156);
lean_dec_ref(x_156);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_182 = x_181;
} else {
 lean_dec_ref(x_181);
 x_182 = lean_box(0);
}
x_183 = lean_box(0);
lean_inc(x_168);
if (lean_is_scalar(x_169)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_169;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_168);
lean_ctor_set(x_184, 1, x_183);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_182;
 lean_ctor_set_tag(x_185, 1);
}
lean_ctor_set(x_185, 0, x_184);
x_186 = l_Lake_buildAction___redArg___lam__0(x_157, x_185, x_167);
lean_dec_ref(x_185);
lean_dec(x_157);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_168);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_inc(x_174);
lean_inc_ref(x_173);
lean_inc_ref(x_170);
lean_dec(x_169);
lean_dec(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_190 = x_167;
} else {
 lean_dec_ref(x_167);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_181, 0);
lean_inc(x_191);
lean_dec_ref(x_181);
x_192 = lean_io_error_to_string(x_191);
x_193 = 3;
x_194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_193);
x_195 = lean_array_push(x_170, x_194);
if (lean_is_scalar(x_190)) {
 x_196 = lean_alloc_ctor(0, 3, 2);
} else {
 x_196 = x_190;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_173);
lean_ctor_set(x_196, 2, x_174);
lean_ctor_set_uint8(x_196, sizeof(void*)*3, x_171);
lean_ctor_set_uint8(x_196, sizeof(void*)*3 + 1, x_172);
x_160 = x_176;
x_161 = x_196;
x_162 = lean_box(0);
goto block_166;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_inc(x_174);
lean_inc_ref(x_173);
lean_inc_ref(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec_ref(x_156);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_197 = x_167;
} else {
 lean_dec_ref(x_167);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_180, 0);
lean_inc(x_198);
lean_dec_ref(x_180);
x_199 = lean_io_error_to_string(x_198);
x_200 = 3;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_push(x_170, x_201);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 3, 2);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_173);
lean_ctor_set(x_203, 2, x_174);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_171);
lean_ctor_set_uint8(x_203, sizeof(void*)*3 + 1, x_172);
x_160 = x_176;
x_161 = x_203;
x_162 = lean_box(0);
goto block_166;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec_ref(x_156);
lean_dec_ref(x_148);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_204 = lean_ctor_get(x_159, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_159, 1);
lean_inc(x_205);
lean_dec_ref(x_159);
x_160 = x_204;
x_161 = x_205;
x_162 = lean_box(0);
goto block_166;
}
block_166:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_box(0);
x_164 = l_Lake_buildAction___redArg___lam__0(x_157, x_163, x_161);
lean_dec(x_157);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_13 = x_160;
x_14 = x_165;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_206 = lean_box(0);
x_207 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_208 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_206, x_207);
x_209 = l_Lake_BuildMetadata_writeFile(x_156, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_209);
x_210 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_211 = lean_array_get_size(x_148);
x_212 = lean_array_push(x_148, x_210);
x_213 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_151);
lean_ctor_set(x_213, 2, x_152);
lean_ctor_set_uint8(x_213, sizeof(void*)*3, x_154);
lean_ctor_set_uint8(x_213, sizeof(void*)*3 + 1, x_153);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_ctor_get(x_209, 0);
lean_inc(x_215);
lean_dec_ref(x_209);
x_216 = lean_io_error_to_string(x_215);
x_217 = 3;
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = lean_array_get_size(x_148);
x_220 = lean_array_push(x_148, x_218);
x_221 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_151);
lean_ctor_set(x_221, 2, x_152);
lean_ctor_set_uint8(x_221, sizeof(void*)*3, x_154);
lean_ctor_set_uint8(x_221, sizeof(void*)*3 + 1, x_153);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_5);
x_18 = l_Lake_readTraceFile(x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set(x_14, 0, x_20);
x_21 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = 0;
x_26 = lean_unbox(x_23);
lean_dec(x_23);
x_27 = l_Lake_instDecidableEqOutputStatus(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_21);
x_30 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_31 = l_Lake_buildAction___redArg(x_30, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = 0;
x_47 = lean_unbox(x_44);
lean_dec(x_44);
x_48 = l_Lake_instDecidableEqOutputStatus(x_47, x_46);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_53 = l_Lake_buildAction___redArg(x_52, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = 0;
x_57 = lean_box(x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
return x_21;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_21, 0);
x_65 = lean_ctor_get(x_21, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_21);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_14, 0, x_68);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_70);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_14);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_74 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_75 = lean_ctor_get(x_14, 1);
x_76 = lean_ctor_get(x_14, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_72);
lean_dec(x_14);
lean_inc_ref(x_5);
x_77 = l_Lake_readTraceFile(x_5, x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_76);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_73);
lean_ctor_set_uint8(x_80, sizeof(void*)*3 + 1, x_74);
x_81 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_78, x_8, x_9, x_10, x_11, x_12, x_13, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = 0;
x_86 = lean_unbox(x_82);
lean_dec(x_82);
x_87 = l_Lake_instDecidableEqOutputStatus(x_86, x_85);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_88 = 1;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_84);
x_91 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_92 = l_Lake_buildAction___redArg(x_91, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_83);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = 0;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_100 = x_92;
} else {
 lean_dec_ref(x_92);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_104 = x_81;
} else {
 lean_dec_ref(x_81);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_77, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_108 = x_77;
} else {
 lean_dec_ref(x_77);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_75);
lean_ctor_set(x_109, 2, x_76);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_73);
lean_ctor_set_uint8(x_109, sizeof(void*)*3 + 1, x_74);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_6);
x_19 = l_Lake_readTraceFile(x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_ctor_set(x_15, 0, x_21);
x_22 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = 0;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
x_28 = l_Lake_instDecidableEqOutputStatus(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_22);
x_31 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_32 = l_Lake_buildAction___redArg(x_31, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = 0;
x_48 = lean_unbox(x_45);
lean_dec(x_45);
x_49 = l_Lake_instDecidableEqOutputStatus(x_48, x_47);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_54 = l_Lake_buildAction___redArg(x_53, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = 0;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_19);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_15, 0, x_69);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_19, 0);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_71);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_15);
return x_72;
}
}
}
else
{
lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_75 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_76 = lean_ctor_get(x_15, 1);
x_77 = lean_ctor_get(x_15, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_73);
lean_dec(x_15);
lean_inc_ref(x_6);
x_78 = l_Lake_readTraceFile(x_6, x_73);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_81, sizeof(void*)*3 + 1, x_75);
x_82 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_79, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = 0;
x_87 = lean_unbox(x_83);
lean_dec(x_83);
x_88 = l_Lake_instDecidableEqOutputStatus(x_87, x_86);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_89 = 1;
x_90 = lean_box(x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_84);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_85);
x_92 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_93 = l_Lake_buildAction___redArg(x_92, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_84);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = 0;
x_97 = lean_box(x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_103 = lean_ctor_get(x_82, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_105 = x_82;
} else {
 lean_dec_ref(x_82);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
x_107 = lean_ctor_get(x_78, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_78, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_109 = x_78;
} else {
 lean_dec_ref(x_78);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_76);
lean_ctor_set(x_110, 2, x_77);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_110, sizeof(void*)*3 + 1, x_75);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_110);
return x_111;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_5);
x_23 = l_Lake_readTraceFile(x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_25);
x_26 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_35; uint8_t x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
x_35 = 0;
x_36 = lean_unbox(x_27);
lean_dec(x_27);
x_37 = l_Lake_instDecidableEqOutputStatus(x_36, x_35);
if (x_37 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_31 = x_28;
x_32 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_39 = l_Lake_buildAction___redArg(x_38, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_31 = x_40;
x_32 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec_ref(x_39);
x_16 = x_41;
x_17 = x_42;
x_18 = lean_box(0);
goto block_20;
}
}
block_34:
{
lean_object* x_33; 
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec_ref(x_26);
x_16 = x_43;
x_17 = x_44;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
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
x_45 = lean_ctor_get(x_23, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_46);
x_16 = x_45;
x_17 = x_14;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_49 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_50 = lean_ctor_get(x_14, 1);
x_51 = lean_ctor_get(x_14, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_47);
lean_dec(x_14);
lean_inc_ref(x_5);
x_52 = l_Lake_readTraceFile(x_5, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_49);
x_56 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_53, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_65; uint8_t x_66; uint8_t x_67; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
x_65 = 0;
x_66 = lean_unbox(x_57);
lean_dec(x_57);
x_67 = l_Lake_instDecidableEqOutputStatus(x_66, x_65);
if (x_67 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_61 = x_58;
x_62 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_69 = l_Lake_buildAction___redArg(x_68, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_58);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_61 = x_70;
x_62 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec_ref(x_69);
x_16 = x_71;
x_17 = x_72;
x_18 = lean_box(0);
goto block_20;
}
}
block_64:
{
lean_object* x_63; 
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec_ref(x_56);
x_16 = x_73;
x_17 = x_74;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
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
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_52, 1);
lean_inc(x_76);
lean_dec_ref(x_52);
x_77 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_50);
lean_ctor_set(x_77, 2, x_51);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_48);
lean_ctor_set_uint8(x_77, sizeof(void*)*3 + 1, x_49);
x_16 = x_75;
x_17 = x_77;
x_18 = lean_box(0);
goto block_20;
}
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_6);
x_24 = l_Lake_readTraceFile(x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_26);
x_27 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_36; uint8_t x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
x_36 = 0;
x_37 = lean_unbox(x_28);
lean_dec(x_28);
x_38 = l_Lake_instDecidableEqOutputStatus(x_37, x_36);
if (x_38 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_32 = x_29;
x_33 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_40 = l_Lake_buildAction___redArg(x_39, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_32 = x_41;
x_33 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_17 = x_42;
x_18 = x_43;
x_19 = lean_box(0);
goto block_21;
}
}
block_35:
{
lean_object* x_34; 
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec_ref(x_27);
x_17 = x_44;
x_18 = x_45;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_47);
x_17 = x_46;
x_18 = x_15;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_50 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_51 = lean_ctor_get(x_15, 1);
x_52 = lean_ctor_get(x_15, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_48);
lean_dec(x_15);
lean_inc_ref(x_6);
x_53 = l_Lake_readTraceFile(x_6, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_50);
x_57 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_54, x_9, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
x_66 = 0;
x_67 = lean_unbox(x_58);
lean_dec(x_58);
x_68 = l_Lake_instDecidableEqOutputStatus(x_67, x_66);
if (x_68 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_62 = x_59;
x_63 = lean_box(0);
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
x_70 = l_Lake_buildAction___redArg(x_69, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_59);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
x_62 = x_71;
x_63 = lean_box(0);
goto block_65;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec_ref(x_70);
x_17 = x_72;
x_18 = x_73;
x_19 = lean_box(0);
goto block_21;
}
}
block_65:
{
lean_object* x_64; 
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
lean_dec_ref(x_57);
x_17 = x_74;
x_18 = x_75;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
x_76 = lean_ctor_get(x_53, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
lean_dec_ref(x_53);
x_78 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_51);
lean_ctor_set(x_78, 2, x_52);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 1, x_50);
x_17 = x_76;
x_18 = x_78;
x_19 = lean_box(0);
goto block_21;
}
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
return x_20;
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
lean_object* x_12; 
x_12 = l_Lake_computeBinFileHash(x_1);
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_13; 
x_13 = l_Lake_computeTextFileHash(x_1);
x_4 = x_13;
goto block_11;
}
block_11:
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
uint8_t x_8; 
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_48; lean_object* x_49; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 1);
x_8 = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(x_1);
x_9 = lean_string_append(x_1, x_8);
if (x_7 == 0)
{
x_48 = x_4;
x_49 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = l_Lake_Hash_load_x3f(x_9);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
else
{
lean_dec(x_63);
x_48 = x_4;
x_49 = lean_box(0);
goto block_62;
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
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_13);
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
x_27 = lean_array_get_size(x_11);
x_28 = lean_array_push(x_11, x_26);
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_13);
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
x_35 = lean_array_get_size(x_11);
x_36 = lean_array_push(x_11, x_34);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_10);
lean_ctor_set(x_37, 2, x_12);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_13);
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
x_43 = lean_array_get_size(x_11);
x_44 = lean_array_push(x_11, x_42);
x_45 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_12);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 1, x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_62:
{
if (x_2 == 0)
{
lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_52 = lean_ctor_get_uint8(x_48, sizeof(void*)*3 + 1);
x_53 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_48, 2);
lean_inc(x_54);
lean_dec_ref(x_48);
x_55 = l_Lake_computeBinFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_53;
x_11 = x_50;
x_12 = x_54;
x_13 = x_51;
x_14 = x_52;
x_15 = x_55;
goto block_47;
}
else
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_48, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_48, 2);
lean_inc(x_60);
lean_dec_ref(x_48);
x_61 = l_Lake_computeTextFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_59;
x_11 = x_56;
x_12 = x_60;
x_13 = x_57;
x_14 = x_58;
x_15 = x_61;
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_io_metadata(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_19 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_ctor_set_uint64(x_19, sizeof(void*)*3, x_20);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
uint8_t x_21; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_8, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec_ref(x_15);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_10);
x_30 = lean_array_push(x_10, x_28);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_29);
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec_ref(x_15);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_10);
x_36 = lean_array_push(x_10, x_34);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_14);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get_uint8(x_38, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_38, 1);
x_44 = lean_ctor_get(x_38, 2);
x_45 = lean_io_metadata(x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_47);
lean_dec(x_46);
x_48 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_49 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_unbox_uint64(x_39);
lean_dec(x_39);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_52 = x_38;
} else {
 lean_dec_ref(x_38);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec_ref(x_45);
x_54 = lean_io_error_to_string(x_53);
x_55 = 3;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_get_size(x_40);
x_58 = lean_array_push(x_40, x_56);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 3, 2);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_59, sizeof(void*)*3 + 1, x_42);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_6);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_3);
x_17 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 2);
x_23 = l_Lake_JobAction_merge(x_21, x_6);
x_24 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_5);
x_25 = l_System_FilePath_addExtension(x_5, x_24);
if (x_22 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_io_mono_ms_now();
lean_inc_ref(x_20);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
x_27 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*3);
x_40 = lean_ctor_get_uint8(x_36, sizeof(void*)*3 + 1);
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 2);
x_43 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_46 = lean_array_get_size(x_38);
x_47 = l_Array_extract___redArg(x_38, x_45, x_46);
x_48 = lean_box(0);
x_49 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_48, x_47);
x_50 = l_Lake_BuildMetadata_writeFile(x_5, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
x_51 = l_Lake_removeFileIfExists(x_25);
lean_dec_ref(x_25);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_inc(x_44);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_54);
lean_ctor_set(x_27, 0, x_44);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_27);
x_55 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_26, x_51, x_36);
lean_dec_ref(x_51);
lean_dec(x_26);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_44);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
x_60 = lean_box(0);
lean_inc(x_44);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_60);
lean_ctor_set(x_27, 0, x_44);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_27);
x_62 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_26, x_61, x_36);
lean_dec_ref(x_61);
lean_dec(x_26);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_44);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_38);
lean_dec(x_44);
lean_free_object(x_27);
x_66 = !lean_is_exclusive(x_36);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_36, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_36, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_36, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
lean_dec_ref(x_51);
x_71 = lean_io_error_to_string(x_70);
x_72 = 3;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_push(x_38, x_73);
lean_ctor_set(x_36, 0, x_74);
x_28 = x_46;
x_29 = x_36;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_36);
x_75 = lean_ctor_get(x_51, 0);
lean_inc(x_75);
lean_dec_ref(x_51);
x_76 = lean_io_error_to_string(x_75);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_push(x_38, x_78);
x_80 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_41);
lean_ctor_set(x_80, 2, x_42);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_39);
lean_ctor_set_uint8(x_80, sizeof(void*)*3 + 1, x_40);
x_28 = x_46;
x_29 = x_80;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
uint8_t x_81; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_38);
lean_dec(x_44);
lean_free_object(x_27);
lean_dec_ref(x_25);
x_81 = !lean_is_exclusive(x_36);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_36, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_36, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_36, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_50, 0);
lean_inc(x_85);
lean_dec_ref(x_50);
x_86 = lean_io_error_to_string(x_85);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_push(x_38, x_88);
lean_ctor_set(x_36, 0, x_89);
x_28 = x_46;
x_29 = x_36;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_36);
x_90 = lean_ctor_get(x_50, 0);
lean_inc(x_90);
lean_dec_ref(x_50);
x_91 = lean_io_error_to_string(x_90);
x_92 = 3;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_array_push(x_38, x_93);
x_95 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_41);
lean_ctor_set(x_95, 2, x_42);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_39);
lean_ctor_set_uint8(x_95, sizeof(void*)*3 + 1, x_40);
x_28 = x_46;
x_29 = x_95;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
uint8_t x_96; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_38);
lean_free_object(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
x_96 = !lean_is_exclusive(x_36);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_36, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_36, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_36, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_43, 0);
lean_inc(x_100);
lean_dec_ref(x_43);
x_101 = lean_io_error_to_string(x_100);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_array_get_size(x_38);
x_105 = lean_array_push(x_38, x_103);
lean_ctor_set(x_36, 0, x_105);
x_28 = x_104;
x_29 = x_36;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_36);
x_106 = lean_ctor_get(x_43, 0);
lean_inc(x_106);
lean_dec_ref(x_43);
x_107 = lean_io_error_to_string(x_106);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_array_get_size(x_38);
x_111 = lean_array_push(x_38, x_109);
x_112 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_41);
lean_ctor_set(x_112, 2, x_42);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_39);
lean_ctor_set_uint8(x_112, sizeof(void*)*3 + 1, x_40);
x_28 = x_110;
x_29 = x_112;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_27, 1);
lean_inc(x_113);
lean_dec(x_27);
x_114 = lean_ctor_get(x_113, 0);
x_115 = lean_ctor_get_uint8(x_113, sizeof(void*)*3);
x_116 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 1);
x_117 = lean_ctor_get(x_113, 1);
x_118 = lean_ctor_get(x_113, 2);
x_119 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_array_get_size(x_20);
lean_dec_ref(x_20);
x_122 = lean_array_get_size(x_114);
x_123 = l_Array_extract___redArg(x_114, x_121, x_122);
x_124 = lean_box(0);
x_125 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_124, x_123);
x_126 = l_Lake_BuildMetadata_writeFile(x_5, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_dec_ref(x_126);
x_127 = l_Lake_removeFileIfExists(x_25);
lean_dec_ref(x_25);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_128 = x_127;
} else {
 lean_dec_ref(x_127);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
lean_inc(x_120);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_128)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_128;
 lean_ctor_set_tag(x_131, 1);
}
lean_ctor_set(x_131, 0, x_130);
x_132 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_26, x_131, x_113);
lean_dec_ref(x_131);
lean_dec(x_26);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_120);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc_ref(x_114);
lean_dec(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 x_136 = x_113;
} else {
 lean_dec_ref(x_113);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
lean_dec_ref(x_127);
x_138 = lean_io_error_to_string(x_137);
x_139 = 3;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_array_push(x_114, x_140);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(0, 3, 2);
} else {
 x_142 = x_136;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_117);
lean_ctor_set(x_142, 2, x_118);
lean_ctor_set_uint8(x_142, sizeof(void*)*3, x_115);
lean_ctor_set_uint8(x_142, sizeof(void*)*3 + 1, x_116);
x_28 = x_122;
x_29 = x_142;
x_30 = lean_box(0);
goto block_34;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc_ref(x_114);
lean_dec(x_120);
lean_dec_ref(x_25);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 x_143 = x_113;
} else {
 lean_dec_ref(x_113);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_126, 0);
lean_inc(x_144);
lean_dec_ref(x_126);
x_145 = lean_io_error_to_string(x_144);
x_146 = 3;
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_array_push(x_114, x_147);
if (lean_is_scalar(x_143)) {
 x_149 = lean_alloc_ctor(0, 3, 2);
} else {
 x_149 = x_143;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_117);
lean_ctor_set(x_149, 2, x_118);
lean_ctor_set_uint8(x_149, sizeof(void*)*3, x_115);
lean_ctor_set_uint8(x_149, sizeof(void*)*3 + 1, x_116);
x_28 = x_122;
x_29 = x_149;
x_30 = lean_box(0);
goto block_34;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc_ref(x_114);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 x_150 = x_113;
} else {
 lean_dec_ref(x_113);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_119, 0);
lean_inc(x_151);
lean_dec_ref(x_119);
x_152 = lean_io_error_to_string(x_151);
x_153 = 3;
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = lean_array_get_size(x_114);
x_156 = lean_array_push(x_114, x_154);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 3, 2);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_117);
lean_ctor_set(x_157, 2, x_118);
lean_ctor_set_uint8(x_157, sizeof(void*)*3, x_115);
lean_ctor_set_uint8(x_157, sizeof(void*)*3 + 1, x_116);
x_28 = x_155;
x_29 = x_157;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_158 = lean_ctor_get(x_27, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_27, 1);
lean_inc(x_159);
lean_dec_ref(x_27);
x_28 = x_158;
x_29 = x_159;
x_30 = lean_box(0);
goto block_34;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_box(0);
x_32 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_26, x_31, x_29);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_13 = x_28;
x_14 = x_33;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_160 = lean_box(0);
x_161 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_162 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_160, x_161);
x_163 = l_Lake_BuildMetadata_writeFile(x_25, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_163);
x_164 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_165 = lean_array_get_size(x_20);
x_166 = lean_array_push(x_20, x_164);
lean_ctor_set(x_11, 0, x_166);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_22);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_11);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
lean_dec_ref(x_163);
x_169 = lean_io_error_to_string(x_168);
x_170 = 3;
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_170);
x_172 = lean_array_get_size(x_20);
x_173 = lean_array_push(x_20, x_171);
lean_ctor_set(x_11, 0, x_173);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_22);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_11);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_175 = lean_ctor_get(x_10, 0);
x_176 = lean_ctor_get(x_11, 0);
x_177 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_178 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_179 = lean_ctor_get(x_11, 1);
x_180 = lean_ctor_get(x_11, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_176);
lean_dec(x_11);
x_181 = lean_ctor_get_uint8(x_175, sizeof(void*)*2 + 2);
x_182 = l_Lake_JobAction_merge(x_177, x_6);
x_183 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_5);
x_184 = l_System_FilePath_addExtension(x_5, x_183);
if (x_181 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_io_mono_ms_now();
lean_inc_ref(x_176);
x_186 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_179);
lean_ctor_set(x_186, 2, x_180);
lean_ctor_set_uint8(x_186, sizeof(void*)*3, x_182);
lean_ctor_set_uint8(x_186, sizeof(void*)*3 + 1, x_178);
x_187 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_186, lean_box(0));
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_195, 0);
x_198 = lean_ctor_get_uint8(x_195, sizeof(void*)*3);
x_199 = lean_ctor_get_uint8(x_195, sizeof(void*)*3 + 1);
x_200 = lean_ctor_get(x_195, 1);
x_201 = lean_ctor_get(x_195, 2);
x_202 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_array_get_size(x_176);
lean_dec_ref(x_176);
x_205 = lean_array_get_size(x_197);
x_206 = l_Array_extract___redArg(x_197, x_204, x_205);
x_207 = lean_box(0);
x_208 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_207, x_206);
x_209 = l_Lake_BuildMetadata_writeFile(x_5, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
lean_dec_ref(x_209);
x_210 = l_Lake_removeFileIfExists(x_184);
lean_dec_ref(x_184);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_211 = x_210;
} else {
 lean_dec_ref(x_210);
 x_211 = lean_box(0);
}
x_212 = lean_box(0);
lean_inc(x_203);
if (lean_is_scalar(x_196)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_196;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_203);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_211)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_211;
 lean_ctor_set_tag(x_214, 1);
}
lean_ctor_set(x_214, 0, x_213);
x_215 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_185, x_214, x_195);
lean_dec_ref(x_214);
lean_dec(x_185);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_203);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_inc(x_201);
lean_inc_ref(x_200);
lean_inc_ref(x_197);
lean_dec(x_203);
lean_dec(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 x_219 = x_195;
} else {
 lean_dec_ref(x_195);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_210, 0);
lean_inc(x_220);
lean_dec_ref(x_210);
x_221 = lean_io_error_to_string(x_220);
x_222 = 3;
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_222);
x_224 = lean_array_push(x_197, x_223);
if (lean_is_scalar(x_219)) {
 x_225 = lean_alloc_ctor(0, 3, 2);
} else {
 x_225 = x_219;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_200);
lean_ctor_set(x_225, 2, x_201);
lean_ctor_set_uint8(x_225, sizeof(void*)*3, x_198);
lean_ctor_set_uint8(x_225, sizeof(void*)*3 + 1, x_199);
x_188 = x_205;
x_189 = x_225;
x_190 = lean_box(0);
goto block_194;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_inc(x_201);
lean_inc_ref(x_200);
lean_inc_ref(x_197);
lean_dec(x_203);
lean_dec(x_196);
lean_dec_ref(x_184);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 x_226 = x_195;
} else {
 lean_dec_ref(x_195);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_209, 0);
lean_inc(x_227);
lean_dec_ref(x_209);
x_228 = lean_io_error_to_string(x_227);
x_229 = 3;
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_array_push(x_197, x_230);
if (lean_is_scalar(x_226)) {
 x_232 = lean_alloc_ctor(0, 3, 2);
} else {
 x_232 = x_226;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_200);
lean_ctor_set(x_232, 2, x_201);
lean_ctor_set_uint8(x_232, sizeof(void*)*3, x_198);
lean_ctor_set_uint8(x_232, sizeof(void*)*3 + 1, x_199);
x_188 = x_205;
x_189 = x_232;
x_190 = lean_box(0);
goto block_194;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_inc(x_201);
lean_inc_ref(x_200);
lean_inc_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_184);
lean_dec_ref(x_176);
lean_dec_ref(x_5);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 x_233 = x_195;
} else {
 lean_dec_ref(x_195);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_202, 0);
lean_inc(x_234);
lean_dec_ref(x_202);
x_235 = lean_io_error_to_string(x_234);
x_236 = 3;
x_237 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_236);
x_238 = lean_array_get_size(x_197);
x_239 = lean_array_push(x_197, x_237);
if (lean_is_scalar(x_233)) {
 x_240 = lean_alloc_ctor(0, 3, 2);
} else {
 x_240 = x_233;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_200);
lean_ctor_set(x_240, 2, x_201);
lean_ctor_set_uint8(x_240, sizeof(void*)*3, x_198);
lean_ctor_set_uint8(x_240, sizeof(void*)*3 + 1, x_199);
x_188 = x_238;
x_189 = x_240;
x_190 = lean_box(0);
goto block_194;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_184);
lean_dec_ref(x_176);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_241 = lean_ctor_get(x_187, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_187, 1);
lean_inc(x_242);
lean_dec_ref(x_187);
x_188 = x_241;
x_189 = x_242;
x_190 = lean_box(0);
goto block_194;
}
block_194:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_box(0);
x_192 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_185, x_191, x_189);
lean_dec(x_185);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_13 = x_188;
x_14 = x_193;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_243 = lean_box(0);
x_244 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_245 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_243, x_244);
x_246 = l_Lake_BuildMetadata_writeFile(x_184, x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_246);
x_247 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_248 = lean_array_get_size(x_176);
x_249 = lean_array_push(x_176, x_247);
x_250 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_179);
lean_ctor_set(x_250, 2, x_180);
lean_ctor_set_uint8(x_250, sizeof(void*)*3, x_182);
lean_ctor_set_uint8(x_250, sizeof(void*)*3 + 1, x_181);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_252 = lean_ctor_get(x_246, 0);
lean_inc(x_252);
lean_dec_ref(x_246);
x_253 = lean_io_error_to_string(x_252);
x_254 = 3;
x_255 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_254);
x_256 = lean_array_get_size(x_176);
x_257 = lean_array_push(x_176, x_255);
x_258 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_179);
lean_ctor_set(x_258, 2, x_180);
lean_ctor_set_uint8(x_258, sizeof(void*)*3, x_182);
lean_ctor_set_uint8(x_258, sizeof(void*)*3 + 1, x_181);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
x_15 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_box_uint64(x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_16);
x_17 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
lean_dec_ref(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_25 = 0;
x_26 = lean_unbox(x_18);
x_27 = l_Lake_instDecidableEqOutputStatus(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_30 = 1;
x_31 = l_Lake_JobAction_merge(x_29, x_30);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_31);
x_32 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_19);
lean_dec_ref(x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_21 = x_33;
x_22 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_40 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 1);
x_41 = lean_ctor_get(x_19, 1);
x_42 = lean_ctor_get(x_19, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_38);
lean_dec(x_19);
x_43 = 1;
x_44 = l_Lake_JobAction_merge(x_39, x_43);
x_45 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*3 + 1, x_40);
x_46 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_45);
lean_dec_ref(x_15);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_21 = x_47;
x_22 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
lean_dec(x_18);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_dec_ref(x_15);
x_21 = x_19;
x_22 = lean_box(0);
goto block_24;
}
block_24:
{
lean_object* x_23; 
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_20;
}
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_65; uint8_t x_66; uint8_t x_67; 
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
lean_dec(x_4);
x_53 = lean_ctor_get_uint64(x_52, sizeof(void*)*3);
x_54 = lean_ctor_get(x_52, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_52);
x_55 = lean_box_uint64(x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_56, x_5, x_9, x_10);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_65 = 0;
x_66 = lean_unbox(x_58);
x_67 = l_Lake_instDecidableEqOutputStatus(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get_uint8(x_59, sizeof(void*)*3);
x_70 = lean_ctor_get_uint8(x_59, sizeof(void*)*3 + 1);
x_71 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_59, 2);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
x_74 = 1;
x_75 = l_Lake_JobAction_merge(x_69, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 3, 2);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*3 + 1, x_70);
x_77 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_54, x_1, x_6, x_7, x_8, x_9, x_76);
lean_dec_ref(x_54);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_61 = x_78;
x_62 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_60);
lean_dec(x_58);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_dec_ref(x_54);
x_61 = x_59;
x_62 = lean_box(0);
goto block_64;
}
block_64:
{
lean_object* x_63; 
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_4);
x_83 = lean_ctor_get(x_9, 0);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
if (x_84 == 0)
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_10);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_2, x_5);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_10);
return x_91;
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_92 = 1;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_10);
return x_94;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; uint8_t x_47; 
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
x_50 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_51 = lean_string_append(x_1, x_50);
lean_inc_ref(x_51);
x_52 = l_Lake_readTraceFile(x_51, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_49, 2);
lean_inc_ref(x_49);
lean_ctor_set(x_9, 0, x_54);
x_56 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_49, x_53, x_55, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = 0;
x_60 = lean_unbox(x_57);
lean_dec(x_57);
x_61 = l_Lake_instDecidableEqOutputStatus(x_60, x_59);
if (x_61 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = x_58;
x_17 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_62; lean_object* x_63; 
x_62 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_63 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_2, x_1, x_4, x_49, x_51, x_62, x_5, x_6, x_7, x_8, x_58);
lean_dec_ref(x_49);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_16 = x_64;
x_17 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_11 = x_65;
x_12 = x_66;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec_ref(x_56);
x_11 = x_67;
x_12 = x_68;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_51);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_dec_ref(x_52);
lean_ctor_set(x_9, 0, x_70);
x_11 = x_69;
x_12 = x_9;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_73 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_74 = lean_ctor_get(x_9, 1);
x_75 = lean_ctor_get(x_9, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_71);
lean_dec(x_9);
x_76 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_77 = lean_string_append(x_1, x_76);
lean_inc_ref(x_77);
x_78 = l_Lake_readTraceFile(x_77, x_71);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_74);
x_82 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_72);
lean_ctor_set_uint8(x_82, sizeof(void*)*3 + 1, x_73);
x_83 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_74, x_79, x_81, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = 0;
x_87 = lean_unbox(x_84);
lean_dec(x_84);
x_88 = l_Lake_instDecidableEqOutputStatus(x_87, x_86);
if (x_88 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = x_85;
x_17 = lean_box(0);
goto block_46;
}
else
{
uint8_t x_89; lean_object* x_90; 
x_89 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_90 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_2, x_1, x_4, x_74, x_77, x_89, x_5, x_6, x_7, x_8, x_85);
lean_dec_ref(x_74);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_16 = x_91;
x_17 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec_ref(x_90);
x_11 = x_92;
x_12 = x_93;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_83, 1);
lean_inc(x_95);
lean_dec_ref(x_83);
x_11 = x_94;
x_12 = x_95;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_77);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_96 = lean_ctor_get(x_78, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_78, 1);
lean_inc(x_97);
lean_dec_ref(x_78);
x_98 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_74);
lean_ctor_set(x_98, 2, x_75);
lean_ctor_set_uint8(x_98, sizeof(void*)*3, x_72);
lean_ctor_set_uint8(x_98, sizeof(void*)*3 + 1, x_73);
x_11 = x_96;
x_12 = x_98;
x_13 = lean_box(0);
goto block_15;
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_46:
{
lean_object* x_18; 
x_18 = l_Lake_fetchFileTrace___redArg(x_1, x_3, x_8, x_16);
lean_dec_ref(x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
x_28 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 1);
x_29 = lean_ctor_get(x_20, 2);
lean_inc(x_29);
lean_inc(x_26);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_28);
lean_ctor_set(x_18, 1, x_31);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_34);
x_35 = lean_ctor_get_uint8(x_32, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_32, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get(x_32, 2);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 3, 2);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*3 + 1, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_19; 
lean_inc_ref(x_1);
x_19 = l_Lake_writeFileHash(x_1, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = lean_io_metadata(x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_22);
lean_dec(x_21);
x_16 = lean_box(0);
x_17 = x_22;
goto block_18;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_20);
x_23 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_16 = lean_box(0);
x_17 = x_23;
goto block_18;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_18:
{
if (x_4 == 0)
{
x_8 = lean_box(0);
x_9 = x_17;
x_10 = x_5;
goto block_15;
}
else
{
lean_dec_ref(x_5);
lean_inc_ref(x_1);
x_8 = lean_box(0);
x_9 = x_17;
x_10 = x_1;
goto block_15;
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
lean_object* x_8; lean_object* x_9; lean_object* x_16; uint8_t x_25; 
x_25 = 1;
if (x_4 == 0)
{
lean_object* x_26; 
x_26 = l_IO_FS_readBinFile(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lake_Hash_nil;
x_29 = lean_byte_array_hash(x_27);
x_30 = lean_uint64_mix_hash(x_28, x_29);
lean_inc_ref(x_3);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_30);
x_32 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
x_33 = l_System_FilePath_join(x_1, x_32);
x_55 = lean_string_utf8_byte_size(x_3);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Lake_Hash_hex(x_30);
x_59 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_string_append(x_60, x_3);
lean_dec_ref(x_3);
x_34 = x_61;
goto block_54;
}
else
{
lean_object* x_62; 
lean_dec_ref(x_3);
x_62 = l_Lake_Hash_hex(x_30);
x_34 = x_62;
goto block_54;
}
block_54:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_35, 0, x_25);
lean_ctor_set_uint8(x_35, 1, x_4);
lean_ctor_set_uint8(x_35, 2, x_5);
lean_inc_ref_n(x_35, 2);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_IO_setAccessRights(x_2, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec_ref(x_37);
x_38 = l_Lake_joinRelative(x_33, x_34);
x_39 = l_System_FilePath_pathExists(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc_ref(x_38);
x_40 = l_Lake_createParentDirs(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
x_41 = lean_io_hard_link(x_2, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
lean_dec_ref(x_36);
lean_dec(x_27);
x_42 = lean_box(0);
x_43 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_30, x_31, x_6, x_38, x_42);
x_16 = x_43;
goto block_24;
}
else
{
lean_object* x_44; 
lean_dec_ref(x_41);
x_44 = l_IO_FS_writeBinFile(x_38, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
x_45 = l_IO_setAccessRights(x_38, x_36);
lean_dec_ref(x_36);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_30, x_31, x_6, x_38, x_46);
x_16 = x_47;
goto block_24;
}
else
{
lean_object* x_48; 
lean_dec_ref(x_38);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec_ref(x_45);
x_8 = x_48;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_31);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
lean_dec_ref(x_44);
x_8 = x_49;
x_9 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_50; 
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_31);
lean_dec(x_27);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec_ref(x_40);
x_8 = x_50;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_36);
lean_dec(x_27);
x_51 = lean_box(0);
x_52 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_30, x_31, x_6, x_38, x_51);
x_16 = x_52;
goto block_24;
}
}
else
{
lean_object* x_53; 
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec(x_27);
lean_dec_ref(x_2);
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec_ref(x_37);
x_8 = x_53;
x_9 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_26, 0);
lean_inc(x_63);
lean_dec_ref(x_26);
x_8 = x_63;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_64; 
x_64 = l_IO_FS_readFile(x_2);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_String_crlfToLf(x_65);
lean_dec(x_65);
x_67 = l_Lake_Hash_nil;
x_68 = lean_string_hash(x_66);
x_69 = lean_uint64_mix_hash(x_67, x_68);
lean_inc_ref(x_3);
x_70 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_69);
x_71 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
x_72 = l_System_FilePath_join(x_1, x_71);
x_90 = lean_string_utf8_byte_size(x_3);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_nat_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = l_Lake_Hash_hex(x_69);
x_94 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_string_append(x_95, x_3);
lean_dec_ref(x_3);
x_73 = x_96;
goto block_89;
}
else
{
lean_object* x_97; 
lean_dec_ref(x_3);
x_97 = l_Lake_Hash_hex(x_69);
x_73 = x_97;
goto block_89;
}
block_89:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_obj_once(&l_Lake_Cache_saveArtifact___closed__3, &l_Lake_Cache_saveArtifact___closed__3_once, _init_l_Lake_Cache_saveArtifact___closed__3);
x_75 = l_IO_setAccessRights(x_2, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_dec_ref(x_75);
x_76 = l_Lake_joinRelative(x_72, x_73);
x_77 = l_System_FilePath_pathExists(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc_ref(x_76);
x_78 = l_Lake_createParentDirs(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_dec_ref(x_78);
x_79 = l_IO_FS_writeFile(x_76, x_66);
lean_dec_ref(x_66);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec_ref(x_79);
x_80 = l_IO_setAccessRights(x_76, x_74);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_69, x_70, x_6, x_76, x_81);
x_16 = x_82;
goto block_24;
}
else
{
lean_object* x_83; 
lean_dec_ref(x_76);
lean_dec_ref(x_70);
lean_dec_ref(x_2);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec_ref(x_80);
x_8 = x_83;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_84; 
lean_dec_ref(x_76);
lean_dec_ref(x_70);
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec_ref(x_79);
x_8 = x_84;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_85; 
lean_dec_ref(x_76);
lean_dec_ref(x_70);
lean_dec_ref(x_66);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
lean_dec_ref(x_78);
x_8 = x_85;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_66);
x_86 = lean_box(0);
x_87 = l_Lake_Cache_saveArtifact___lam__0(x_2, x_69, x_70, x_6, x_76, x_86);
x_16 = x_87;
goto block_24;
}
}
else
{
lean_object* x_88; 
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_66);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_75, 0);
lean_inc(x_88);
lean_dec_ref(x_75);
x_8 = x_88;
x_9 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_64, 0);
lean_inc(x_98);
lean_dec_ref(x_64);
x_8 = x_98;
x_9 = lean_box(0);
goto block_15;
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
x_11 = lean_io_error_to_string(x_8);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_mk_io_user_error(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec_ref(x_16);
x_8 = x_23;
x_9 = lean_box(0);
goto block_15;
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_5, 6);
x_256 = lean_ctor_get(x_255, 25);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_10, 1);
x_258 = lean_ctor_get(x_257, 1);
x_259 = lean_ctor_get(x_258, 6);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_257, 0);
x_261 = lean_ctor_get(x_260, 6);
x_262 = lean_ctor_get(x_261, 25);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
x_263 = 0;
x_94 = x_263;
x_95 = x_11;
x_96 = lean_box(0);
goto block_254;
}
else
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_unbox(x_264);
x_94 = x_265;
x_95 = x_11;
x_96 = lean_box(0);
goto block_254;
}
}
else
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_259, 0);
x_267 = lean_unbox(x_266);
x_94 = x_267;
x_95 = x_11;
x_96 = lean_box(0);
goto block_254;
}
}
else
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_ctor_get(x_256, 0);
x_269 = lean_unbox(x_268);
x_94 = x_269;
x_95 = x_11;
x_96 = lean_box(0);
goto block_254;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
block_93:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_33; uint64_t x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_3);
x_34 = lean_ctor_get_uint64(x_33, sizeof(void*)*3);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_uint64_dec_eq(x_34, x_2);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_31;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc(x_37);
x_38 = lean_apply_8(x_1, x_37, x_26, x_27, x_28, x_29, x_30, x_31, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 1)
{
if (x_25 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_18 = x_41;
x_19 = x_40;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_38, 1);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec_ref(x_39);
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get_uint8(x_43, sizeof(void*)*3);
x_48 = lean_ctor_get_uint8(x_43, sizeof(void*)*3 + 1);
x_49 = lean_ctor_get(x_43, 1);
x_50 = lean_ctor_get(x_43, 2);
x_51 = lean_box(0);
x_52 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_4, x_24, x_2, x_37, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
lean_free_object(x_38);
x_18 = x_45;
x_19 = x_43;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_53; 
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc_ref(x_46);
lean_dec(x_45);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_43, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_43, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec_ref(x_52);
x_58 = lean_io_error_to_string(x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_46);
x_62 = lean_array_push(x_46, x_60);
lean_ctor_set(x_43, 0, x_62);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_61);
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_43);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec_ref(x_52);
x_64 = lean_io_error_to_string(x_63);
x_65 = 3;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_array_get_size(x_46);
x_68 = lean_array_push(x_46, x_66);
x_69 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_47);
lean_ctor_set_uint8(x_69, sizeof(void*)*3 + 1, x_48);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_69);
lean_ctor_set(x_38, 0, x_67);
return x_38;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_dec(x_38);
x_71 = lean_ctor_get(x_39, 0);
lean_inc(x_71);
lean_dec_ref(x_39);
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get_uint8(x_70, sizeof(void*)*3);
x_74 = lean_ctor_get_uint8(x_70, sizeof(void*)*3 + 1);
x_75 = lean_ctor_get(x_70, 1);
x_76 = lean_ctor_get(x_70, 2);
x_77 = lean_box(0);
x_78 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_4, x_24, x_2, x_37, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_78);
x_18 = x_71;
x_19 = x_70;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_76);
lean_inc_ref(x_75);
lean_inc_ref(x_72);
lean_dec(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 x_79 = x_70;
} else {
 lean_dec_ref(x_70);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_io_error_to_string(x_80);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_get_size(x_72);
x_85 = lean_array_push(x_72, x_83);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(0, 3, 2);
} else {
 x_86 = x_79;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_75);
lean_ctor_set(x_86, 2, x_76);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_73);
lean_ctor_set_uint8(x_86, sizeof(void*)*3 + 1, x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
lean_dec_ref(x_38);
x_13 = x_88;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
uint8_t x_89; 
lean_dec(x_37);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
x_89 = !lean_is_exclusive(x_38);
if (x_89 == 0)
{
return x_38;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_38, 0);
x_91 = lean_ctor_get(x_38, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_38);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_dec(x_35);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_31;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_31;
x_14 = lean_box(0);
goto block_17;
}
}
block_254:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_99);
lean_inc_ref(x_4);
x_100 = l_Lake_Cache_readOutputs_x3f(x_4, x_99, x_2, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
lean_ctor_set(x_95, 0, x_102);
if (lean_obj_tag(x_101) == 1)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_105 = lean_apply_8(x_1, x_104, x_6, x_7, x_8, x_9, x_10, x_95, lean_box(0));
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_free_object(x_101);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = l_Lake_Hash_hex(x_2);
x_112 = lean_string_utf8_byte_size(x_111);
x_113 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_111);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_112);
x_115 = lean_unsigned_to_nat(7u);
x_116 = l_String_Slice_Pos_nextn(x_114, x_113, x_115);
lean_dec_ref(x_114);
x_117 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_111);
lean_ctor_set(x_118, 1, x_113);
lean_ctor_set(x_118, 2, x_116);
x_119 = l_String_Slice_toString(x_118);
lean_dec_ref(x_118);
x_120 = lean_string_append(x_117, x_119);
lean_dec_ref(x_119);
x_121 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_string_append(x_122, x_108);
lean_dec(x_108);
x_124 = 2;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_push(x_110, x_125);
lean_ctor_set(x_107, 0, x_126);
x_24 = x_99;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_107;
x_32 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_127 = lean_ctor_get(x_107, 0);
x_128 = lean_ctor_get_uint8(x_107, sizeof(void*)*3);
x_129 = lean_ctor_get_uint8(x_107, sizeof(void*)*3 + 1);
x_130 = lean_ctor_get(x_107, 1);
x_131 = lean_ctor_get(x_107, 2);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_127);
lean_dec(x_107);
x_132 = l_Lake_Hash_hex(x_2);
x_133 = lean_string_utf8_byte_size(x_132);
x_134 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_132);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_133);
x_136 = lean_unsigned_to_nat(7u);
x_137 = l_String_Slice_Pos_nextn(x_135, x_134, x_136);
lean_dec_ref(x_135);
x_138 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_137);
x_140 = l_String_Slice_toString(x_139);
lean_dec_ref(x_139);
x_141 = lean_string_append(x_138, x_140);
lean_dec_ref(x_140);
x_142 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_108);
lean_dec(x_108);
x_145 = 2;
x_146 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_145);
x_147 = lean_array_push(x_127, x_146);
x_148 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_130);
lean_ctor_set(x_148, 2, x_131);
lean_ctor_set_uint8(x_148, sizeof(void*)*3, x_128);
lean_ctor_set_uint8(x_148, sizeof(void*)*3 + 1, x_129);
x_24 = x_99;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_148;
x_32 = lean_box(0);
goto block_93;
}
}
else
{
uint8_t x_149; 
lean_dec_ref(x_99);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_149 = !lean_is_exclusive(x_105);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_105, 0);
lean_dec(x_150);
x_151 = lean_ctor_get(x_106, 0);
lean_inc(x_151);
lean_dec_ref(x_106);
lean_ctor_set(x_101, 0, x_151);
lean_ctor_set(x_105, 0, x_101);
return x_105;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_105, 1);
lean_inc(x_152);
lean_dec(x_105);
x_153 = lean_ctor_get(x_106, 0);
lean_inc(x_153);
lean_dec_ref(x_106);
lean_ctor_set(x_101, 0, x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_101);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_free_object(x_101);
lean_dec_ref(x_99);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_155 = !lean_is_exclusive(x_105);
if (x_155 == 0)
{
return x_105;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_105, 0);
x_157 = lean_ctor_get(x_105, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_105);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_101, 0);
lean_inc(x_159);
lean_dec(x_101);
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_160 = lean_apply_8(x_1, x_159, x_6, x_7, x_8, x_9, x_10, x_95, lean_box(0));
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec_ref(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc_ref(x_164);
x_165 = lean_ctor_get_uint8(x_162, sizeof(void*)*3);
x_166 = lean_ctor_get_uint8(x_162, sizeof(void*)*3 + 1);
x_167 = lean_ctor_get(x_162, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_162, 2);
lean_inc(x_168);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_169 = x_162;
} else {
 lean_dec_ref(x_162);
 x_169 = lean_box(0);
}
x_170 = l_Lake_Hash_hex(x_2);
x_171 = lean_string_utf8_byte_size(x_170);
x_172 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_170);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_171);
x_174 = lean_unsigned_to_nat(7u);
x_175 = l_String_Slice_Pos_nextn(x_173, x_172, x_174);
lean_dec_ref(x_173);
x_176 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_172);
lean_ctor_set(x_177, 2, x_175);
x_178 = l_String_Slice_toString(x_177);
lean_dec_ref(x_177);
x_179 = lean_string_append(x_176, x_178);
lean_dec_ref(x_178);
x_180 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
x_181 = lean_string_append(x_179, x_180);
x_182 = lean_string_append(x_181, x_163);
lean_dec(x_163);
x_183 = 2;
x_184 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set_uint8(x_184, sizeof(void*)*1, x_183);
x_185 = lean_array_push(x_164, x_184);
if (lean_is_scalar(x_169)) {
 x_186 = lean_alloc_ctor(0, 3, 2);
} else {
 x_186 = x_169;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_167);
lean_ctor_set(x_186, 2, x_168);
lean_ctor_set_uint8(x_186, sizeof(void*)*3, x_165);
lean_ctor_set_uint8(x_186, sizeof(void*)*3 + 1, x_166);
x_24 = x_99;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_186;
x_32 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_99);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_187 = lean_ctor_get(x_160, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_188 = x_160;
} else {
 lean_dec_ref(x_160);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_161, 0);
lean_inc(x_189);
lean_dec_ref(x_161);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_188;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec_ref(x_99);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_192 = lean_ctor_get(x_160, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_160, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_194 = x_160;
} else {
 lean_dec_ref(x_160);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
else
{
lean_dec(x_101);
x_24 = x_99;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_95;
x_32 = lean_box(0);
goto block_93;
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_99);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_196 = !lean_is_exclusive(x_100);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_100, 1);
lean_ctor_set(x_95, 0, x_197);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_100, 0);
x_199 = lean_ctor_get(x_100, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_100);
lean_ctor_set(x_95, 0, x_199);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_95);
return x_200;
}
}
}
else
{
lean_object* x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_95, 0);
x_202 = lean_ctor_get_uint8(x_95, sizeof(void*)*3);
x_203 = lean_ctor_get_uint8(x_95, sizeof(void*)*3 + 1);
x_204 = lean_ctor_get(x_95, 1);
x_205 = lean_ctor_get(x_95, 2);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_201);
lean_dec(x_95);
x_206 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_206);
lean_inc_ref(x_4);
x_207 = l_Lake_Cache_readOutputs_x3f(x_4, x_206, x_2, x_201);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set_uint8(x_210, sizeof(void*)*3, x_202);
lean_ctor_set_uint8(x_210, sizeof(void*)*3 + 1, x_203);
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_208, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_213 = lean_apply_8(x_1, x_211, x_6, x_7, x_8, x_9, x_10, x_210, lean_box(0));
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec_ref(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_217);
x_218 = lean_ctor_get_uint8(x_215, sizeof(void*)*3);
x_219 = lean_ctor_get_uint8(x_215, sizeof(void*)*3 + 1);
x_220 = lean_ctor_get(x_215, 1);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_215, 2);
lean_inc(x_221);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 x_222 = x_215;
} else {
 lean_dec_ref(x_215);
 x_222 = lean_box(0);
}
x_223 = l_Lake_Hash_hex(x_2);
x_224 = lean_string_utf8_byte_size(x_223);
x_225 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_223);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_224);
x_227 = lean_unsigned_to_nat(7u);
x_228 = l_String_Slice_Pos_nextn(x_226, x_225, x_227);
lean_dec_ref(x_226);
x_229 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_225);
lean_ctor_set(x_230, 2, x_228);
x_231 = l_String_Slice_toString(x_230);
lean_dec_ref(x_230);
x_232 = lean_string_append(x_229, x_231);
lean_dec_ref(x_231);
x_233 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
x_234 = lean_string_append(x_232, x_233);
x_235 = lean_string_append(x_234, x_216);
lean_dec(x_216);
x_236 = 2;
x_237 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_236);
x_238 = lean_array_push(x_217, x_237);
if (lean_is_scalar(x_222)) {
 x_239 = lean_alloc_ctor(0, 3, 2);
} else {
 x_239 = x_222;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_220);
lean_ctor_set(x_239, 2, x_221);
lean_ctor_set_uint8(x_239, sizeof(void*)*3, x_218);
lean_ctor_set_uint8(x_239, sizeof(void*)*3 + 1, x_219);
x_24 = x_206;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_239;
x_32 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_206);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_240 = lean_ctor_get(x_213, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_241 = x_213;
} else {
 lean_dec_ref(x_213);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_214, 0);
lean_inc(x_242);
lean_dec_ref(x_214);
if (lean_is_scalar(x_212)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_212;
}
lean_ctor_set(x_243, 0, x_242);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_240);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_212);
lean_dec_ref(x_206);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_245 = lean_ctor_get(x_213, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_213, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_247 = x_213;
} else {
 lean_dec_ref(x_213);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_dec(x_208);
x_24 = x_206;
x_25 = x_94;
x_26 = x_6;
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_210;
x_32 = lean_box(0);
goto block_93;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec_ref(x_206);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_249 = lean_ctor_get(x_207, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_207, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_251 = x_207;
} else {
 lean_dec_ref(x_207);
 x_251 = lean_box(0);
}
x_252 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_204);
lean_ctor_set(x_252, 2, x_205);
lean_ctor_set_uint8(x_252, sizeof(void*)*3, x_202);
lean_ctor_set_uint8(x_252, sizeof(void*)*3 + 1, x_203);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_14 = l_Lake_getArtifacts_x3f___redArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_getArtifacts_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_15 = l_Lake_getArtifacts_x3f(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_Cache_getArtifact___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_inc(x_4);
x_9 = l_Lake_ArtifactDescr_fromJson_x3f(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_13 = lean_unsigned_to_nat(80u);
x_14 = l_Lean_Json_pretty(x_4, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_apply_2(x_8, lean_box(0), x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_22 = lean_unsigned_to_nat(80u);
x_23 = l_Lean_Json_pretty(x_4, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec(x_20);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_apply_2(x_8, lean_box(0), x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec_ref(x_9);
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec_ref(x_7);
x_32 = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
x_33 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1), 3, 2);
lean_closure_set(x_33, 0, x_30);
lean_closure_set(x_33, 1, x_2);
x_34 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_32, x_1);
x_35 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_34, x_33);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_inc(x_5);
x_10 = l_Lake_ArtifactDescr_fromJson_x3f(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_14 = lean_unsigned_to_nat(80u);
x_15 = l_Lean_Json_pretty(x_5, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_apply_2(x_9, lean_box(0), x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_5, x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_21);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_apply_2(x_9, lean_box(0), x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
lean_dec(x_5);
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec_ref(x_10);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec_ref(x_8);
x_33 = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
x_34 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1), 3, 2);
lean_closure_set(x_34, 0, x_31);
lean_closure_set(x_34, 1, x_3);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_2);
x_36 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_35, x_34);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f), 5, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_19 = lean_io_metadata(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_21);
lean_dec(x_20);
x_11 = lean_box(0);
x_12 = x_9;
x_13 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_19);
x_22 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_11 = lean_box(0);
x_12 = x_9;
x_13 = x_22;
goto block_18;
}
block_18:
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
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
lean_object* x_6; lean_object* x_7; uint8_t x_17; 
x_17 = l_System_FilePath_pathExists(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_37 = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
x_38 = lean_string_append(x_37, x_19);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_push(x_4, x_40);
lean_inc_ref(x_1);
x_42 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec_ref(x_42);
x_43 = lean_io_hard_link(x_19, x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_20 = x_41;
x_21 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_string_append(x_45, x_46);
lean_dec_ref(x_46);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_39);
x_49 = lean_array_push(x_41, x_48);
x_50 = l_Lake_copyFile(x_19, x_1);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_50);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, 1, x_17);
lean_ctor_set_uint8(x_52, 2, x_3);
lean_inc_ref_n(x_52, 2);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_IO_setAccessRights(x_1, x_53);
lean_dec_ref(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_20 = x_49;
x_21 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_io_error_to_string(x_55);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_49);
x_60 = lean_array_push(x_49, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
x_63 = lean_io_error_to_string(x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_49);
x_67 = lean_array_push(x_49, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_42, 0);
lean_inc(x_69);
lean_dec_ref(x_42);
x_70 = lean_io_error_to_string(x_69);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_get_size(x_41);
x_74 = lean_array_push(x_41, x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
block_36:
{
uint64_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get_uint64(x_18, sizeof(void*)*1);
x_23 = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
x_24 = lean_string_append(x_23, x_1);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_array_push(x_20, x_26);
lean_inc_ref(x_1);
x_28 = l_Lake_writeFileHash(x_1, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
x_6 = x_27;
x_7 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_io_error_to_string(x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_27);
x_34 = lean_array_push(x_27, x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
x_6 = x_4;
x_7 = lean_box(0);
goto block_16;
}
block_16:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
lean_inc_ref(x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_3);
x_17 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 2);
x_26 = l_Lake_JobAction_merge(x_24, x_9);
x_27 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_8);
x_28 = l_System_FilePath_addExtension(x_8, x_27);
if (x_25 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; 
x_29 = lean_io_mono_ms_now();
x_37 = l_Lake_removeFileIfExists(x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
lean_inc_ref(x_23);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_26);
lean_inc_ref(x_13);
x_38 = lean_apply_7(x_2, x_6, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_39, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 2);
lean_inc_ref(x_1);
x_45 = l_Lake_clearFileHash(x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec_ref(x_45);
x_46 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_47 = x_46;
} else {
 lean_dec_ref(x_46);
 x_47 = lean_box(0);
}
x_48 = l_Lake_computeArtifact___redArg(x_1, x_4, x_5, x_13, x_39);
lean_dec_ref(x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*3);
x_55 = lean_ctor_get_uint8(x_49, sizeof(void*)*3 + 1);
x_56 = lean_ctor_get(x_49, 1);
x_57 = lean_ctor_get(x_49, 2);
x_58 = lean_ctor_get_uint64(x_52, sizeof(void*)*1);
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_array_get_size(x_23);
lean_dec_ref(x_23);
x_61 = lean_array_get_size(x_53);
x_62 = l_Array_extract___redArg(x_53, x_60, x_61);
x_115 = lean_string_utf8_byte_size(x_59);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = l_Lake_Hash_hex(x_58);
x_119 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_59);
x_63 = x_121;
goto block_114;
}
else
{
lean_object* x_122; 
x_122 = l_Lake_Hash_hex(x_58);
x_63 = x_122;
goto block_114;
}
block_114:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_47)) {
 x_64 = lean_alloc_ctor(3, 1, 0);
} else {
 x_64 = x_47;
 lean_ctor_set_tag(x_64, 3);
}
lean_ctor_set(x_64, 0, x_63);
x_65 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_64, x_62);
x_66 = l_Lake_BuildMetadata_writeFile(x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
lean_dec_ref(x_66);
x_67 = l_Lake_removeFileIfExists(x_28);
lean_dec_ref(x_28);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_inc(x_50);
if (lean_is_scalar(x_51)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_51;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_71);
x_72 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_29, x_67, x_49);
lean_dec_ref(x_67);
lean_dec(x_29);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_50);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_50);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_67);
x_77 = lean_box(0);
lean_inc(x_50);
if (lean_is_scalar(x_51)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_51;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_50);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_29, x_79, x_49);
lean_dec_ref(x_79);
lean_dec(x_29);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc_ref(x_53);
lean_dec(x_51);
lean_dec(x_50);
x_84 = !lean_is_exclusive(x_49);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_49, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_49, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_49, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
lean_dec_ref(x_67);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_push(x_53, x_91);
lean_ctor_set(x_49, 0, x_92);
x_30 = x_61;
x_31 = x_49;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_49);
x_93 = lean_ctor_get(x_67, 0);
lean_inc(x_93);
lean_dec_ref(x_67);
x_94 = lean_io_error_to_string(x_93);
x_95 = 3;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_array_push(x_53, x_96);
x_98 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_56);
lean_ctor_set(x_98, 2, x_57);
lean_ctor_set_uint8(x_98, sizeof(void*)*3, x_54);
lean_ctor_set_uint8(x_98, sizeof(void*)*3 + 1, x_55);
x_30 = x_61;
x_31 = x_98;
x_32 = lean_box(0);
goto block_36;
}
}
}
else
{
uint8_t x_99; 
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc_ref(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_28);
x_99 = !lean_is_exclusive(x_49);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_49, 2);
lean_dec(x_100);
x_101 = lean_ctor_get(x_49, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_49, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_66, 0);
lean_inc(x_103);
lean_dec_ref(x_66);
x_104 = lean_io_error_to_string(x_103);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_array_push(x_53, x_106);
lean_ctor_set(x_49, 0, x_107);
x_30 = x_61;
x_31 = x_49;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_49);
x_108 = lean_ctor_get(x_66, 0);
lean_inc(x_108);
lean_dec_ref(x_66);
x_109 = lean_io_error_to_string(x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_push(x_53, x_111);
x_113 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_56);
lean_ctor_set(x_113, 2, x_57);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_54);
lean_ctor_set_uint8(x_113, sizeof(void*)*3 + 1, x_55);
x_30 = x_61;
x_31 = x_113;
x_32 = lean_box(0);
goto block_36;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_47);
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_8);
x_123 = lean_ctor_get(x_48, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_48, 1);
lean_inc(x_124);
lean_dec_ref(x_48);
x_30 = x_123;
x_31 = x_124;
x_32 = lean_box(0);
goto block_36;
}
}
else
{
uint8_t x_125; 
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc_ref(x_40);
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_39);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_39, 2);
lean_dec(x_126);
x_127 = lean_ctor_get(x_39, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_39, 0);
lean_dec(x_128);
x_129 = lean_ctor_get(x_46, 0);
lean_inc(x_129);
lean_dec_ref(x_46);
x_130 = lean_io_error_to_string(x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_get_size(x_40);
x_134 = lean_array_push(x_40, x_132);
lean_ctor_set(x_39, 0, x_134);
x_30 = x_133;
x_31 = x_39;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_39);
x_135 = lean_ctor_get(x_46, 0);
lean_inc(x_135);
lean_dec_ref(x_46);
x_136 = lean_io_error_to_string(x_135);
x_137 = 3;
x_138 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_137);
x_139 = lean_array_get_size(x_40);
x_140 = lean_array_push(x_40, x_138);
x_141 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_43);
lean_ctor_set(x_141, 2, x_44);
lean_ctor_set_uint8(x_141, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_141, sizeof(void*)*3 + 1, x_42);
x_30 = x_139;
x_31 = x_141;
x_32 = lean_box(0);
goto block_36;
}
}
}
else
{
uint8_t x_142; 
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc_ref(x_40);
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_39);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_39, 2);
lean_dec(x_143);
x_144 = lean_ctor_get(x_39, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_39, 0);
lean_dec(x_145);
x_146 = lean_ctor_get(x_45, 0);
lean_inc(x_146);
lean_dec_ref(x_45);
x_147 = lean_io_error_to_string(x_146);
x_148 = 3;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_get_size(x_40);
x_151 = lean_array_push(x_40, x_149);
lean_ctor_set(x_39, 0, x_151);
x_30 = x_150;
x_31 = x_39;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_39);
x_152 = lean_ctor_get(x_45, 0);
lean_inc(x_152);
lean_dec_ref(x_45);
x_153 = lean_io_error_to_string(x_152);
x_154 = 3;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_array_get_size(x_40);
x_157 = lean_array_push(x_40, x_155);
x_158 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_43);
lean_ctor_set(x_158, 2, x_44);
lean_ctor_set_uint8(x_158, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_158, sizeof(void*)*3 + 1, x_42);
x_30 = x_156;
x_31 = x_158;
x_32 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_159 = lean_ctor_get(x_38, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_38, 1);
lean_inc(x_160);
lean_dec_ref(x_38);
x_30 = x_159;
x_31 = x_160;
x_32 = lean_box(0);
goto block_36;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_28);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_161 = lean_ctor_get(x_37, 0);
lean_inc(x_161);
lean_dec_ref(x_37);
x_162 = lean_io_error_to_string(x_161);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_get_size(x_23);
x_166 = lean_array_push(x_23, x_164);
lean_ctor_set(x_14, 0, x_166);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_26);
x_30 = x_165;
x_31 = x_14;
x_32 = lean_box(0);
goto block_36;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_box(0);
x_34 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_29, x_33, x_31);
lean_dec(x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_16 = x_30;
x_17 = x_35;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = lean_box(0);
x_168 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_169 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_167, x_168);
x_170 = l_Lake_BuildMetadata_writeFile(x_28, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_170);
x_171 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_172 = lean_array_get_size(x_23);
x_173 = lean_array_push(x_23, x_171);
lean_ctor_set(x_14, 0, x_173);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_25);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_14);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_170, 0);
lean_inc(x_175);
lean_dec_ref(x_170);
x_176 = lean_io_error_to_string(x_175);
x_177 = 3;
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_177);
x_179 = lean_array_get_size(x_23);
x_180 = lean_array_push(x_23, x_178);
lean_ctor_set(x_14, 0, x_180);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_25);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_14);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_13, 0);
x_183 = lean_ctor_get(x_14, 0);
x_184 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_185 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_186 = lean_ctor_get(x_14, 1);
x_187 = lean_ctor_get(x_14, 2);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_183);
lean_dec(x_14);
x_188 = lean_ctor_get_uint8(x_182, sizeof(void*)*2 + 2);
x_189 = l_Lake_JobAction_merge(x_184, x_9);
x_190 = ((lean_object*)(l_Lake_buildAction___redArg___closed__0));
lean_inc_ref(x_8);
x_191 = l_System_FilePath_addExtension(x_8, x_190);
if (x_188 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_200; 
x_192 = lean_io_mono_ms_now();
x_200 = l_Lake_removeFileIfExists(x_1);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_200);
lean_inc_ref(x_183);
x_201 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_201, 0, x_183);
lean_ctor_set(x_201, 1, x_186);
lean_ctor_set(x_201, 2, x_187);
lean_ctor_set_uint8(x_201, sizeof(void*)*3, x_189);
lean_ctor_set_uint8(x_201, sizeof(void*)*3 + 1, x_185);
lean_inc_ref(x_13);
x_202 = lean_apply_7(x_2, x_6, x_10, x_11, x_12, x_13, x_201, lean_box(0));
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec_ref(x_202);
x_204 = lean_ctor_get(x_203, 0);
x_205 = lean_ctor_get_uint8(x_203, sizeof(void*)*3);
x_206 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 1);
x_207 = lean_ctor_get(x_203, 1);
x_208 = lean_ctor_get(x_203, 2);
lean_inc_ref(x_1);
x_209 = l_Lake_clearFileHash(x_1);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
lean_dec_ref(x_209);
x_210 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_211 = x_210;
} else {
 lean_dec_ref(x_210);
 x_211 = lean_box(0);
}
x_212 = l_Lake_computeArtifact___redArg(x_1, x_4, x_5, x_13, x_203);
lean_dec_ref(x_13);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; uint64_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_213, 0);
x_218 = lean_ctor_get_uint8(x_213, sizeof(void*)*3);
x_219 = lean_ctor_get_uint8(x_213, sizeof(void*)*3 + 1);
x_220 = lean_ctor_get(x_213, 1);
x_221 = lean_ctor_get(x_213, 2);
x_222 = lean_ctor_get_uint64(x_216, sizeof(void*)*1);
x_223 = lean_ctor_get(x_216, 0);
x_224 = lean_array_get_size(x_183);
lean_dec_ref(x_183);
x_225 = lean_array_get_size(x_217);
x_226 = l_Array_extract___redArg(x_217, x_224, x_225);
x_255 = lean_string_utf8_byte_size(x_223);
x_256 = lean_unsigned_to_nat(0u);
x_257 = lean_nat_dec_eq(x_255, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = l_Lake_Hash_hex(x_222);
x_259 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_260 = lean_string_append(x_258, x_259);
x_261 = lean_string_append(x_260, x_223);
x_227 = x_261;
goto block_254;
}
else
{
lean_object* x_262; 
x_262 = l_Lake_Hash_hex(x_222);
x_227 = x_262;
goto block_254;
}
block_254:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
if (lean_is_scalar(x_211)) {
 x_228 = lean_alloc_ctor(3, 1, 0);
} else {
 x_228 = x_211;
 lean_ctor_set_tag(x_228, 3);
}
lean_ctor_set(x_228, 0, x_227);
x_229 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_228, x_226);
x_230 = l_Lake_BuildMetadata_writeFile(x_8, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
lean_dec_ref(x_230);
x_231 = l_Lake_removeFileIfExists(x_191);
lean_dec_ref(x_191);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_232 = x_231;
} else {
 lean_dec_ref(x_231);
 x_232 = lean_box(0);
}
x_233 = lean_box(0);
lean_inc(x_214);
if (lean_is_scalar(x_215)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_215;
 lean_ctor_set_tag(x_234, 1);
}
lean_ctor_set(x_234, 0, x_214);
lean_ctor_set(x_234, 1, x_233);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_232;
 lean_ctor_set_tag(x_235, 1);
}
lean_ctor_set(x_235, 0, x_234);
x_236 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_192, x_235, x_213);
lean_dec_ref(x_235);
lean_dec(x_192);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_214);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_inc(x_221);
lean_inc_ref(x_220);
lean_inc_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 x_240 = x_213;
} else {
 lean_dec_ref(x_213);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_231, 0);
lean_inc(x_241);
lean_dec_ref(x_231);
x_242 = lean_io_error_to_string(x_241);
x_243 = 3;
x_244 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_243);
x_245 = lean_array_push(x_217, x_244);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(0, 3, 2);
} else {
 x_246 = x_240;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_220);
lean_ctor_set(x_246, 2, x_221);
lean_ctor_set_uint8(x_246, sizeof(void*)*3, x_218);
lean_ctor_set_uint8(x_246, sizeof(void*)*3 + 1, x_219);
x_193 = x_225;
x_194 = x_246;
x_195 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_inc(x_221);
lean_inc_ref(x_220);
lean_inc_ref(x_217);
lean_dec(x_215);
lean_dec(x_214);
lean_dec_ref(x_191);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 x_247 = x_213;
} else {
 lean_dec_ref(x_213);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_230, 0);
lean_inc(x_248);
lean_dec_ref(x_230);
x_249 = lean_io_error_to_string(x_248);
x_250 = 3;
x_251 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_250);
x_252 = lean_array_push(x_217, x_251);
if (lean_is_scalar(x_247)) {
 x_253 = lean_alloc_ctor(0, 3, 2);
} else {
 x_253 = x_247;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_220);
lean_ctor_set(x_253, 2, x_221);
lean_ctor_set_uint8(x_253, sizeof(void*)*3, x_218);
lean_ctor_set_uint8(x_253, sizeof(void*)*3 + 1, x_219);
x_193 = x_225;
x_194 = x_253;
x_195 = lean_box(0);
goto block_199;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_211);
lean_dec_ref(x_191);
lean_dec_ref(x_183);
lean_dec_ref(x_8);
x_263 = lean_ctor_get(x_212, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_212, 1);
lean_inc(x_264);
lean_dec_ref(x_212);
x_193 = x_263;
x_194 = x_264;
x_195 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_inc(x_208);
lean_inc_ref(x_207);
lean_inc_ref(x_204);
lean_dec_ref(x_191);
lean_dec_ref(x_183);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 x_265 = x_203;
} else {
 lean_dec_ref(x_203);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_210, 0);
lean_inc(x_266);
lean_dec_ref(x_210);
x_267 = lean_io_error_to_string(x_266);
x_268 = 3;
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_268);
x_270 = lean_array_get_size(x_204);
x_271 = lean_array_push(x_204, x_269);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 3, 2);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_207);
lean_ctor_set(x_272, 2, x_208);
lean_ctor_set_uint8(x_272, sizeof(void*)*3, x_205);
lean_ctor_set_uint8(x_272, sizeof(void*)*3 + 1, x_206);
x_193 = x_270;
x_194 = x_272;
x_195 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_inc(x_208);
lean_inc_ref(x_207);
lean_inc_ref(x_204);
lean_dec_ref(x_191);
lean_dec_ref(x_183);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 x_273 = x_203;
} else {
 lean_dec_ref(x_203);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_209, 0);
lean_inc(x_274);
lean_dec_ref(x_209);
x_275 = lean_io_error_to_string(x_274);
x_276 = 3;
x_277 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*1, x_276);
x_278 = lean_array_get_size(x_204);
x_279 = lean_array_push(x_204, x_277);
if (lean_is_scalar(x_273)) {
 x_280 = lean_alloc_ctor(0, 3, 2);
} else {
 x_280 = x_273;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_207);
lean_ctor_set(x_280, 2, x_208);
lean_ctor_set_uint8(x_280, sizeof(void*)*3, x_205);
lean_ctor_set_uint8(x_280, sizeof(void*)*3 + 1, x_206);
x_193 = x_278;
x_194 = x_280;
x_195 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec_ref(x_191);
lean_dec_ref(x_183);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_202, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_202, 1);
lean_inc(x_282);
lean_dec_ref(x_202);
x_193 = x_281;
x_194 = x_282;
x_195 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_191);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_283 = lean_ctor_get(x_200, 0);
lean_inc(x_283);
lean_dec_ref(x_200);
x_284 = lean_io_error_to_string(x_283);
x_285 = 3;
x_286 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*1, x_285);
x_287 = lean_array_get_size(x_183);
x_288 = lean_array_push(x_183, x_286);
x_289 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_186);
lean_ctor_set(x_289, 2, x_187);
lean_ctor_set_uint8(x_289, sizeof(void*)*3, x_189);
lean_ctor_set_uint8(x_289, sizeof(void*)*3 + 1, x_185);
x_193 = x_287;
x_194 = x_289;
x_195 = lean_box(0);
goto block_199;
}
block_199:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_box(0);
x_197 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_192, x_196, x_194);
lean_dec(x_192);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec_ref(x_197);
x_16 = x_193;
x_17 = x_198;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_290 = lean_box(0);
x_291 = lean_obj_once(&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1, &l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_once, _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
x_292 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_290, x_291);
x_293 = l_Lake_BuildMetadata_writeFile(x_191, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec_ref(x_293);
x_294 = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
x_295 = lean_array_get_size(x_183);
x_296 = lean_array_push(x_183, x_294);
x_297 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_186);
lean_ctor_set(x_297, 2, x_187);
lean_ctor_set_uint8(x_297, sizeof(void*)*3, x_189);
lean_ctor_set_uint8(x_297, sizeof(void*)*3 + 1, x_188);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_293, 0);
lean_inc(x_299);
lean_dec_ref(x_293);
x_300 = lean_io_error_to_string(x_299);
x_301 = 3;
x_302 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*1, x_301);
x_303 = lean_array_get_size(x_183);
x_304 = lean_array_push(x_183, x_302);
x_305 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_186);
lean_ctor_set(x_305, 2, x_187);
lean_ctor_set_uint8(x_305, sizeof(void*)*3, x_189);
lean_ctor_set_uint8(x_305, sizeof(void*)*3 + 1, x_188);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_4, 6);
x_201 = lean_ctor_get(x_200, 25);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_5, 1);
x_203 = lean_ctor_get(x_202, 1);
x_204 = lean_ctor_get(x_203, 6);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_202, 0);
x_206 = lean_ctor_get(x_205, 6);
x_207 = lean_ctor_get(x_206, 25);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = 0;
x_90 = x_208;
x_91 = x_6;
x_92 = lean_box(0);
goto block_199;
}
else
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_unbox(x_209);
x_90 = x_210;
x_91 = x_6;
x_92 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_204, 0);
x_212 = lean_unbox(x_211);
x_90 = x_212;
x_91 = x_6;
x_92 = lean_box(0);
goto block_199;
}
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_201, 0);
x_214 = lean_unbox(x_213);
x_90 = x_214;
x_91 = x_6;
x_92 = lean_box(0);
goto block_199;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_62:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_24; uint64_t x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_2);
x_25 = lean_ctor_get_uint64(x_24, sizeof(void*)*3);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_uint64_dec_eq(x_25, x_1);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
x_8 = x_22;
x_9 = lean_box(0);
goto block_12;
}
else
{
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_28);
x_29 = l_Lake_ArtifactDescr_fromJson_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
x_8 = x_22;
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec_ref(x_21);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_22, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get(x_22, 1);
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_30, 3);
lean_inc_ref(x_37);
lean_dec(x_30);
x_38 = l_Lake_Cache_getArtifact(x_37, x_31);
if (lean_obj_tag(x_38) == 0)
{
if (x_19 == 0)
{
lean_object* x_39; 
lean_dec(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_13 = x_39;
x_14 = x_22;
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_box(0);
x_42 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_3, x_20, x_1, x_28, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_13 = x_40;
x_14 = x_22;
x_15 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_43; 
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_32);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_22, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_22, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_22, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec_ref(x_42);
x_48 = lean_io_error_to_string(x_47);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_32);
x_52 = lean_array_push(x_32, x_50);
lean_ctor_set(x_22, 0, x_52);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_22);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_22);
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec_ref(x_42);
x_55 = lean_io_error_to_string(x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_32);
x_59 = lean_array_push(x_32, x_57);
x_60 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_35);
lean_ctor_set(x_60, 2, x_36);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_33);
lean_ctor_set_uint8(x_60, sizeof(void*)*3 + 1, x_34);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_dec_ref(x_38);
lean_dec(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
x_8 = x_22;
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
x_8 = x_22;
x_9 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_3);
lean_dec(x_2);
x_8 = x_22;
x_9 = lean_box(0);
goto block_12;
}
}
block_89:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_72 = l_Lake_Hash_hex(x_1);
x_73 = lean_string_utf8_byte_size(x_72);
x_74 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_72);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_73);
x_76 = lean_unsigned_to_nat(7u);
x_77 = l_String_Slice_Pos_nextn(x_75, x_74, x_76);
lean_dec_ref(x_75);
x_78 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_77);
x_80 = l_String_Slice_toString(x_79);
lean_dec_ref(x_79);
x_81 = lean_string_append(x_78, x_80);
lean_dec_ref(x_80);
x_82 = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_string_append(x_83, x_65);
lean_dec_ref(x_65);
x_85 = 2;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_array_push(x_66, x_86);
x_88 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_69);
lean_ctor_set(x_88, 2, x_70);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_67);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 1, x_68);
x_19 = x_63;
x_20 = x_64;
x_21 = x_5;
x_22 = x_88;
x_23 = lean_box(0);
goto block_62;
}
block_199:
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_91, 0);
x_95 = lean_ctor_get_uint8(x_91, sizeof(void*)*3);
x_96 = lean_ctor_get_uint8(x_91, sizeof(void*)*3 + 1);
x_97 = lean_ctor_get(x_91, 1);
x_98 = lean_ctor_get(x_91, 2);
x_99 = l_Lake_Package_cacheScope(x_4);
lean_inc_ref(x_99);
lean_inc_ref(x_3);
x_100 = l_Lake_Cache_readOutputs_x3f(x_3, x_99, x_1, x_94);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc(x_103);
lean_ctor_set(x_91, 0, x_103);
if (lean_obj_tag(x_102) == 1)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = l_Lake_ArtifactDescr_fromJson_x3f(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_102);
lean_dec_ref(x_91);
lean_free_object(x_100);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_109 = lean_unsigned_to_nat(80u);
x_110 = l_Lean_Json_pretty(x_105, x_109);
x_111 = lean_string_append(x_108, x_110);
lean_dec_ref(x_110);
x_112 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_string_append(x_113, x_107);
lean_dec(x_107);
x_63 = x_90;
x_64 = x_99;
x_65 = x_114;
x_66 = x_103;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_105);
x_115 = lean_ctor_get(x_5, 1);
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec_ref(x_106);
x_117 = lean_ctor_get(x_115, 3);
lean_inc_ref(x_117);
x_118 = l_Lake_Cache_getArtifact(x_117, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_103);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
lean_ctor_set(x_102, 0, x_119);
lean_ctor_set(x_100, 1, x_91);
return x_100;
}
else
{
lean_object* x_120; 
lean_free_object(x_102);
lean_dec_ref(x_91);
lean_free_object(x_100);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec_ref(x_118);
x_63 = x_90;
x_64 = x_99;
x_65 = x_120;
x_66 = x_103;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
lean_dec(x_102);
lean_inc(x_121);
x_122 = l_Lake_ArtifactDescr_fromJson_x3f(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_91);
lean_free_object(x_100);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_125 = lean_unsigned_to_nat(80u);
x_126 = l_Lean_Json_pretty(x_121, x_125);
x_127 = lean_string_append(x_124, x_126);
lean_dec_ref(x_126);
x_128 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_string_append(x_129, x_123);
lean_dec(x_123);
x_63 = x_90;
x_64 = x_99;
x_65 = x_130;
x_66 = x_103;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_121);
x_131 = lean_ctor_get(x_5, 1);
x_132 = lean_ctor_get(x_122, 0);
lean_inc(x_132);
lean_dec_ref(x_122);
x_133 = lean_ctor_get(x_131, 3);
lean_inc_ref(x_133);
x_134 = l_Lake_Cache_getArtifact(x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_103);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 0, x_136);
return x_100;
}
else
{
lean_object* x_137; 
lean_dec_ref(x_91);
lean_free_object(x_100);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec_ref(x_134);
x_63 = x_90;
x_64 = x_99;
x_65 = x_137;
x_66 = x_103;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
}
}
}
else
{
lean_free_object(x_100);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_98);
lean_dec_ref(x_97);
x_19 = x_90;
x_20 = x_99;
x_21 = x_5;
x_22 = x_91;
x_23 = lean_box(0);
goto block_62;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_100, 0);
x_139 = lean_ctor_get(x_100, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_100);
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc(x_139);
lean_ctor_set(x_91, 0, x_139);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
lean_inc(x_140);
x_142 = l_Lake_ArtifactDescr_fromJson_x3f(x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_141);
lean_dec_ref(x_91);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_145 = lean_unsigned_to_nat(80u);
x_146 = l_Lean_Json_pretty(x_140, x_145);
x_147 = lean_string_append(x_144, x_146);
lean_dec_ref(x_146);
x_148 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_string_append(x_149, x_143);
lean_dec(x_143);
x_63 = x_90;
x_64 = x_99;
x_65 = x_150;
x_66 = x_139;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_140);
x_151 = lean_ctor_get(x_5, 1);
x_152 = lean_ctor_get(x_142, 0);
lean_inc(x_152);
lean_dec_ref(x_142);
x_153 = lean_ctor_get(x_151, 3);
lean_inc_ref(x_153);
x_154 = l_Lake_Cache_getArtifact(x_153, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_139);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
if (lean_is_scalar(x_141)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_141;
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_91);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_141);
lean_dec_ref(x_91);
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
lean_dec_ref(x_154);
x_63 = x_90;
x_64 = x_99;
x_65 = x_158;
x_66 = x_139;
x_67 = x_95;
x_68 = x_96;
x_69 = x_97;
x_70 = x_98;
x_71 = lean_box(0);
goto block_89;
}
}
}
else
{
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_98);
lean_dec_ref(x_97);
x_19 = x_90;
x_20 = x_99;
x_21 = x_5;
x_22 = x_91;
x_23 = lean_box(0);
goto block_62;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_99);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_100);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_100, 1);
lean_ctor_set(x_91, 0, x_160);
lean_ctor_set(x_100, 1, x_91);
return x_100;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_100, 0);
x_162 = lean_ctor_get(x_100, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_100);
lean_ctor_set(x_91, 0, x_162);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_91);
return x_163;
}
}
}
else
{
lean_object* x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_91, 0);
x_165 = lean_ctor_get_uint8(x_91, sizeof(void*)*3);
x_166 = lean_ctor_get_uint8(x_91, sizeof(void*)*3 + 1);
x_167 = lean_ctor_get(x_91, 1);
x_168 = lean_ctor_get(x_91, 2);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_164);
lean_dec(x_91);
x_169 = l_Lake_Package_cacheScope(x_4);
lean_inc_ref(x_169);
lean_inc_ref(x_3);
x_170 = l_Lake_Cache_readOutputs_x3f(x_3, x_169, x_1, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
lean_inc(x_168);
lean_inc_ref(x_167);
lean_inc(x_172);
x_174 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_167);
lean_ctor_set(x_174, 2, x_168);
lean_ctor_set_uint8(x_174, sizeof(void*)*3, x_165);
lean_ctor_set_uint8(x_174, sizeof(void*)*3 + 1, x_166);
if (lean_obj_tag(x_171) == 1)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
lean_inc(x_175);
x_177 = l_Lake_ArtifactDescr_fromJson_x3f(x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_176);
lean_dec_ref(x_174);
lean_dec(x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0));
x_180 = lean_unsigned_to_nat(80u);
x_181 = l_Lean_Json_pretty(x_175, x_180);
x_182 = lean_string_append(x_179, x_181);
lean_dec_ref(x_181);
x_183 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1));
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_string_append(x_184, x_178);
lean_dec(x_178);
x_63 = x_90;
x_64 = x_169;
x_65 = x_185;
x_66 = x_172;
x_67 = x_165;
x_68 = x_166;
x_69 = x_167;
x_70 = x_168;
x_71 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_175);
x_186 = lean_ctor_get(x_5, 1);
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
lean_dec_ref(x_177);
x_188 = lean_ctor_get(x_186, 3);
lean_inc_ref(x_188);
x_189 = l_Lake_Cache_getArtifact(x_188, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_172);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec_ref(x_167);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
if (lean_is_scalar(x_176)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_176;
}
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_173)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_173;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_174);
return x_192;
}
else
{
lean_object* x_193; 
lean_dec(x_176);
lean_dec_ref(x_174);
lean_dec(x_173);
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
lean_dec_ref(x_189);
x_63 = x_90;
x_64 = x_169;
x_65 = x_193;
x_66 = x_172;
x_67 = x_165;
x_68 = x_166;
x_69 = x_167;
x_70 = x_168;
x_71 = lean_box(0);
goto block_89;
}
}
}
else
{
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_168);
lean_dec_ref(x_167);
x_19 = x_90;
x_20 = x_169;
x_21 = x_5;
x_22 = x_174;
x_23 = lean_box(0);
goto block_62;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_169);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_194 = lean_ctor_get(x_170, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_170, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_196 = x_170;
} else {
 lean_dec_ref(x_170);
 x_196 = lean_box(0);
}
x_197 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_167);
lean_ctor_set(x_197, 2, x_168);
lean_ctor_set_uint8(x_197, sizeof(void*)*3, x_165);
lean_ctor_set_uint8(x_197, sizeof(void*)*3 + 1, x_166);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_9 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_13 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_2);
x_16 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_1, x_2, x_3, x_4, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_75; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
x_75 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get_uint8(x_78, sizeof(void*)*3);
x_82 = lean_ctor_get_uint8(x_78, sizeof(void*)*3 + 1);
x_83 = lean_ctor_get(x_78, 1);
x_84 = lean_ctor_get(x_78, 2);
x_85 = l_Lake_removeFileIfExists(x_5);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_111; uint64_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_86 = x_85;
} else {
 lean_dec_ref(x_85);
 x_86 = lean_box(0);
}
x_111 = lean_ctor_get(x_20, 0);
x_112 = lean_ctor_get_uint64(x_111, sizeof(void*)*1);
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_string_utf8_byte_size(x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = l_Lake_Hash_hex(x_112);
x_118 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_string_append(x_119, x_113);
x_87 = x_120;
goto block_110;
}
else
{
lean_object* x_121; 
x_121 = l_Lake_Hash_hex(x_112);
x_87 = x_121;
goto block_110;
}
block_110:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(3, 1, 0);
} else {
 x_88 = x_86;
 lean_ctor_set_tag(x_88, 3);
}
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lake_BuildMetadata_ofFetch(x_1, x_88);
x_90 = l_Lake_BuildMetadata_writeFile(x_7, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_dec_ref(x_90);
lean_dec(x_79);
x_21 = x_78;
x_22 = lean_box(0);
goto block_74;
}
else
{
uint8_t x_91; 
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc_ref(x_80);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_5);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = lean_ctor_get(x_78, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_78, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_78, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec_ref(x_90);
x_96 = lean_io_error_to_string(x_95);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_80);
x_100 = lean_array_push(x_80, x_98);
lean_ctor_set(x_78, 0, x_100);
if (lean_is_scalar(x_79)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_79;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_78);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_78);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
lean_dec_ref(x_90);
x_103 = lean_io_error_to_string(x_102);
x_104 = 3;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_array_get_size(x_80);
x_107 = lean_array_push(x_80, x_105);
x_108 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_83);
lean_ctor_set(x_108, 2, x_84);
lean_ctor_set_uint8(x_108, sizeof(void*)*3, x_81);
lean_ctor_set_uint8(x_108, sizeof(void*)*3 + 1, x_82);
if (lean_is_scalar(x_79)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_79;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_122; 
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc_ref(x_80);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_122 = !lean_is_exclusive(x_78);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_123 = lean_ctor_get(x_78, 2);
lean_dec(x_123);
x_124 = lean_ctor_get(x_78, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_78, 0);
lean_dec(x_125);
x_126 = lean_ctor_get(x_85, 0);
lean_inc(x_126);
lean_dec_ref(x_85);
x_127 = lean_io_error_to_string(x_126);
x_128 = 3;
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_128);
x_130 = lean_array_get_size(x_80);
x_131 = lean_array_push(x_80, x_129);
lean_ctor_set(x_78, 0, x_131);
if (lean_is_scalar(x_79)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_79;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_78);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_78);
x_133 = lean_ctor_get(x_85, 0);
lean_inc(x_133);
lean_dec_ref(x_85);
x_134 = lean_io_error_to_string(x_133);
x_135 = 3;
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_135);
x_137 = lean_array_get_size(x_80);
x_138 = lean_array_push(x_80, x_136);
x_139 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_83);
lean_ctor_set(x_139, 2, x_84);
lean_ctor_set_uint8(x_139, sizeof(void*)*3, x_81);
lean_ctor_set_uint8(x_139, sizeof(void*)*3 + 1, x_82);
if (lean_is_scalar(x_79)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_79;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; 
lean_dec_ref(x_7);
x_141 = lean_ctor_get(x_75, 1);
lean_inc(x_141);
lean_dec_ref(x_75);
x_21 = x_141;
x_22 = lean_box(0);
goto block_74;
}
}
else
{
uint8_t x_142; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_142 = !lean_is_exclusive(x_75);
if (x_142 == 0)
{
return x_75;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_75, 0);
x_144 = lean_ctor_get(x_75, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_75);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
block_74:
{
if (x_8 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_5);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_inc(x_20);
lean_dec(x_19);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = l_Lake_restoreArtifact(x_5, x_20, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_ctor_set(x_21, 0, x_31);
lean_ctor_set(x_17, 0, x_30);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 0, x_17);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_21, 0, x_33);
lean_ctor_set(x_17, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_21);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_17);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 1);
lean_ctor_set(x_21, 0, x_36);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_21, 0, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_21);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_21, 1);
x_44 = lean_ctor_get(x_21, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_40);
lean_dec(x_21);
x_45 = l_Lake_restoreArtifact(x_5, x_20, x_6, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_42);
lean_ctor_set(x_17, 0, x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_17);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_54, sizeof(void*)*3 + 1, x_42);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_17);
x_56 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_21, 2);
lean_inc(x_60);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_61 = x_21;
} else {
 lean_dec_ref(x_21);
 x_61 = lean_box(0);
}
x_62 = l_Lake_restoreArtifact(x_5, x_20, x_6, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 3, 2);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_57);
lean_ctor_set_uint8(x_66, sizeof(void*)*3 + 1, x_58);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_63);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_72 = lean_alloc_ctor(0, 3, 2);
} else {
 x_72 = x_61;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_57);
lean_ctor_set_uint8(x_72, sizeof(void*)*3 + 1, x_58);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_16);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_16, 0);
lean_dec(x_147);
x_148 = lean_box(0);
lean_ctor_set(x_16, 0, x_148);
return x_16;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_16, 1);
lean_inc(x_149);
lean_dec(x_16);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_8);
x_19 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint64_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; uint8_t x_19; 
x_18 = 1;
x_19 = l_Lake_instDecidableEqOutputStatus(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get(x_16, 1);
x_25 = lean_ctor_get(x_16, 2);
x_26 = lean_ctor_get(x_20, 3);
lean_inc_ref(x_26);
lean_dec(x_20);
x_27 = l_Lake_Cache_saveArtifact(x_26, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lake_Package_cacheScope(x_7);
x_34 = lean_box(0);
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
x_35 = x_65;
goto block_58;
}
else
{
lean_object* x_66; 
x_66 = l_Lake_Hash_hex(x_31);
x_35 = x_66;
goto block_58;
}
block_58:
{
lean_object* x_36; lean_object* x_37; 
if (lean_is_scalar(x_29)) {
 x_36 = lean_alloc_ctor(3, 1, 0);
} else {
 x_36 = x_29;
 lean_ctor_set_tag(x_36, 3);
}
lean_ctor_set(x_36, 0, x_35);
x_37 = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(x_8, x_33, x_9, x_36, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_16);
return x_38;
}
else
{
uint8_t x_39; 
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc_ref(x_21);
lean_dec(x_28);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_16, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_16, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec_ref(x_37);
x_44 = lean_io_error_to_string(x_43);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_21);
x_48 = lean_array_push(x_21, x_46);
lean_ctor_set(x_16, 0, x_48);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_16);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_16);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec_ref(x_37);
x_51 = lean_io_error_to_string(x_50);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_21);
x_55 = lean_array_push(x_21, x_53);
x_56 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_67; 
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc_ref(x_21);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_16, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_16, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_27, 0);
lean_inc(x_71);
lean_dec_ref(x_27);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_21);
x_76 = lean_array_push(x_21, x_74);
lean_ctor_set(x_16, 0, x_76);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_16);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
x_78 = lean_ctor_get(x_27, 0);
lean_inc(x_78);
lean_dec_ref(x_27);
x_79 = lean_io_error_to_string(x_78);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_get_size(x_21);
x_83 = lean_array_push(x_21, x_81);
x_84 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_24);
lean_ctor_set(x_84, 2, x_25);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_84, sizeof(void*)*3 + 1, x_23);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_86 = l_Lake_computeArtifact___redArg(x_2, x_3, x_4, x_15, x_16);
lean_dec_ref(x_15);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint64_t x_22; lean_object* x_23; 
x_18 = lean_unbox(x_1);
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = lean_unbox(x_6);
x_22 = lean_unbox_uint64(x_9);
lean_dec_ref(x_9);
x_23 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_18, x_2, x_3, x_19, x_20, x_21, x_7, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
x_42 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_43 = lean_string_append(x_1, x_42);
lean_inc_ref(x_43);
x_44 = l_Lake_readTraceFile(x_43, x_40);
if (lean_obj_tag(x_44) == 0)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_96; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_122; lean_object* x_123; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_45 = lean_ctor_get(x_11, 1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec_ref(x_44);
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
x_51 = lean_ctor_get(x_45, 3);
x_52 = lean_ctor_get_uint64(x_41, sizeof(void*)*3);
x_53 = lean_ctor_get(x_41, 2);
x_68 = lean_ctor_get(x_48, 6);
x_69 = lean_ctor_get(x_48, 23);
lean_inc(x_69);
x_100 = lean_ctor_get(x_68, 25);
x_101 = lean_ctor_get_uint8(x_68, sizeof(void*)*26 + 4);
lean_inc_ref(x_41);
lean_ctor_set(x_12, 0, x_47);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_50, 6);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_49, 6);
x_182 = lean_ctor_get(x_181, 25);
if (lean_obj_tag(x_182) == 0)
{
x_122 = x_12;
x_123 = lean_box(0);
goto block_144;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_182, 0);
x_184 = lean_unbox(x_183);
x_176 = x_184;
x_177 = x_12;
x_178 = lean_box(0);
goto block_179;
}
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_180, 0);
x_186 = lean_unbox(x_185);
x_176 = x_186;
x_177 = x_12;
x_178 = lean_box(0);
goto block_179;
}
}
else
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_100, 0);
x_188 = lean_unbox(x_187);
x_176 = x_188;
x_177 = x_12;
x_178 = lean_box(0);
goto block_179;
}
block_67:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lake_CacheMap_insertCore(x_52, x_64, x_56);
x_66 = lean_st_ref_set(x_60, x_65);
lean_dec(x_60);
x_14 = x_54;
x_15 = x_59;
x_16 = x_61;
x_17 = x_58;
x_18 = x_55;
x_19 = lean_box(0);
goto block_23;
}
block_95:
{
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec_ref(x_69);
x_74 = lean_st_ref_take(x_73);
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
x_78 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 1);
x_79 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_71, 2);
lean_inc(x_80);
lean_dec_ref(x_71);
x_81 = lean_ctor_get_uint64(x_75, sizeof(void*)*1);
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_string_utf8_byte_size(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = l_Lake_Hash_hex(x_81);
x_87 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_string_append(x_88, x_82);
x_54 = x_70;
x_55 = x_80;
x_56 = x_74;
x_57 = lean_box(0);
x_58 = x_78;
x_59 = x_76;
x_60 = x_73;
x_61 = x_77;
x_62 = x_79;
x_63 = x_89;
goto block_67;
}
else
{
lean_object* x_90; 
x_90 = l_Lake_Hash_hex(x_81);
x_54 = x_70;
x_55 = x_80;
x_56 = x_74;
x_57 = lean_box(0);
x_58 = x_78;
x_59 = x_76;
x_60 = x_73;
x_61 = x_77;
x_62 = x_79;
x_63 = x_90;
goto block_67;
}
}
else
{
lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; 
lean_dec(x_69);
x_91 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
x_93 = lean_ctor_get_uint8(x_71, sizeof(void*)*3 + 1);
x_94 = lean_ctor_get(x_71, 2);
lean_inc(x_94);
lean_dec_ref(x_71);
x_14 = x_70;
x_15 = x_91;
x_16 = x_92;
x_17 = x_93;
x_18 = x_94;
x_19 = lean_box(0);
goto block_23;
}
}
block_99:
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_70 = x_97;
x_71 = x_98;
x_72 = lean_box(0);
goto block_95;
}
else
{
lean_dec(x_69);
return x_96;
}
}
block_115:
{
lean_object* x_105; 
lean_inc_ref(x_11);
lean_inc_ref(x_43);
lean_inc_ref(x_1);
lean_inc(x_48);
lean_inc_ref(x_51);
x_105 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_52, x_46, x_51, x_48, x_1, x_6, x_43, x_102, x_7, x_8, x_9, x_10, x_11, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
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
x_70 = x_108;
x_71 = x_107;
x_72 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_106);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec_ref(x_105);
x_110 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_41, x_43, x_7, x_8, x_9, x_10, x_11, x_109);
lean_dec_ref(x_41);
x_96 = x_110;
goto block_99;
}
}
else
{
uint8_t x_111; 
lean_dec(x_69);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = !lean_is_exclusive(x_105);
if (x_111 == 0)
{
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_105, 0);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_105);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
block_121:
{
if (x_117 == 0)
{
lean_object* x_120; 
lean_dec(x_46);
x_120 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_41, x_43, x_7, x_8, x_9, x_10, x_11, x_118);
lean_dec_ref(x_41);
x_96 = x_120;
goto block_99;
}
else
{
x_102 = x_116;
x_103 = x_118;
x_104 = lean_box(0);
goto block_115;
}
}
block_144:
{
lean_object* x_124; 
lean_inc(x_46);
x_124 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_41, x_46, x_53, x_8, x_9, x_10, x_11, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = 0;
x_128 = lean_unbox(x_125);
lean_dec(x_125);
x_129 = l_Lake_instDecidableEqOutputStatus(x_128, x_127);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_46);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_130 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_126);
lean_dec_ref(x_11);
x_96 = x_130;
goto block_99;
}
else
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_50, 6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_49, 6);
x_133 = lean_ctor_get(x_132, 25);
if (lean_obj_tag(x_133) == 0)
{
x_102 = x_129;
x_103 = x_126;
x_104 = lean_box(0);
goto block_115;
}
else
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
x_135 = lean_unbox(x_134);
x_116 = x_129;
x_117 = x_135;
x_118 = x_126;
x_119 = lean_box(0);
goto block_121;
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_unbox(x_136);
x_116 = x_129;
x_117 = x_137;
x_118 = x_126;
x_119 = lean_box(0);
goto block_121;
}
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_100, 0);
x_139 = lean_unbox(x_138);
x_116 = x_129;
x_117 = x_139;
x_118 = x_126;
x_119 = lean_box(0);
goto block_121;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_69);
lean_dec(x_46);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = !lean_is_exclusive(x_124);
if (x_140 == 0)
{
return x_124;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_124, 0);
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_124);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
block_175:
{
lean_object* x_148; 
lean_inc_ref(x_11);
lean_inc_ref(x_43);
lean_inc_ref(x_1);
lean_inc(x_48);
lean_inc_ref(x_51);
lean_inc(x_46);
x_148 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_52, x_46, x_51, x_48, x_1, x_6, x_43, x_147, x_7, x_8, x_9, x_10, x_11, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 1)
{
lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_51);
lean_dec(x_48);
lean_dec(x_46);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec_ref(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec_ref(x_149);
x_70 = x_151;
x_71 = x_150;
x_72 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_149);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec_ref(x_148);
x_153 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_41, x_46, x_53, x_8, x_9, x_10, x_11, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = 0;
x_157 = lean_unbox(x_154);
x_158 = l_Lake_instDecidableEqOutputStatus(x_157, x_156);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; 
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_2);
x_159 = lean_box(0);
x_160 = lean_unbox(x_154);
lean_dec(x_154);
x_161 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_160, x_1, x_4, x_3, x_6, x_147, x_48, x_51, x_52, x_159, x_7, x_8, x_9, x_10, x_11, x_155);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_96 = x_161;
goto block_99;
}
else
{
lean_object* x_162; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_162 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_41, x_43, x_7, x_8, x_9, x_10, x_11, x_155);
lean_dec_ref(x_41);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_box(0);
x_165 = lean_unbox(x_154);
lean_dec(x_154);
x_166 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_165, x_1, x_4, x_3, x_6, x_147, x_48, x_51, x_52, x_164, x_7, x_8, x_9, x_10, x_11, x_163);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_96 = x_166;
goto block_99;
}
else
{
lean_dec(x_154);
lean_dec(x_69);
lean_dec_ref(x_51);
lean_dec(x_48);
lean_dec_ref(x_8);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_162;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_69);
lean_dec_ref(x_51);
lean_dec(x_48);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_153);
if (x_167 == 0)
{
return x_153;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_153, 0);
x_169 = lean_ctor_get(x_153, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_153);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_69);
lean_dec_ref(x_51);
lean_dec(x_48);
lean_dec(x_46);
lean_dec_ref(x_8);
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_171 = !lean_is_exclusive(x_148);
if (x_171 == 0)
{
return x_148;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_148, 0);
x_173 = lean_ctor_get(x_148, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_148);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
block_179:
{
if (x_176 == 0)
{
x_122 = x_177;
x_123 = lean_box(0);
goto block_144;
}
else
{
lean_inc_ref(x_51);
lean_inc(x_48);
if (x_5 == 0)
{
x_145 = x_177;
x_146 = lean_box(0);
x_147 = x_101;
goto block_175;
}
else
{
x_145 = x_177;
x_146 = lean_box(0);
x_147 = x_5;
goto block_175;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_44, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_44, 1);
lean_inc(x_190);
lean_dec_ref(x_44);
x_191 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_41);
lean_ctor_set(x_12, 0, x_190);
x_192 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_41, x_189, x_191, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_195 = 0;
x_196 = lean_unbox(x_193);
lean_dec(x_193);
x_197 = l_Lake_instDecidableEqOutputStatus(x_196, x_195);
if (x_197 == 0)
{
lean_object* x_198; 
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_198 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_194);
lean_dec_ref(x_11);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_24 = x_199;
x_25 = x_200;
x_26 = lean_box(0);
goto block_38;
}
else
{
return x_198;
}
}
else
{
lean_object* x_201; 
x_201 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_41, x_43, x_7, x_8, x_9, x_10, x_11, x_194);
lean_dec_ref(x_41);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
x_24 = x_202;
x_25 = x_203;
x_26 = lean_box(0);
goto block_38;
}
else
{
return x_201;
}
}
}
else
{
uint8_t x_204; 
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_192);
if (x_204 == 0)
{
return x_192;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_192, 0);
x_206 = lean_ctor_get(x_192, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_192);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec_ref(x_43);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_44);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_44, 1);
lean_ctor_set(x_12, 0, x_209);
lean_ctor_set(x_44, 1, x_12);
return x_44;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_44, 0);
x_211 = lean_ctor_get(x_44, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_44);
lean_ctor_set(x_12, 0, x_211);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_12);
return x_212;
}
}
}
else
{
lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_12, 0);
x_214 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_215 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_216 = lean_ctor_get(x_12, 1);
x_217 = lean_ctor_get(x_12, 2);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_213);
lean_dec(x_12);
x_218 = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(x_1);
x_219 = lean_string_append(x_1, x_218);
lean_inc_ref(x_219);
x_220 = l_Lake_readTraceFile(x_219, x_213);
if (lean_obj_tag(x_220) == 0)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint64_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_272; lean_object* x_276; uint8_t x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; uint8_t x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_298; lean_object* x_299; lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_356; 
x_221 = lean_ctor_get(x_11, 1);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec_ref(x_220);
x_224 = lean_ctor_get(x_8, 0);
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
x_227 = lean_ctor_get(x_221, 3);
x_228 = lean_ctor_get_uint64(x_216, sizeof(void*)*3);
x_229 = lean_ctor_get(x_216, 2);
x_244 = lean_ctor_get(x_224, 6);
x_245 = lean_ctor_get(x_224, 23);
lean_inc(x_245);
x_276 = lean_ctor_get(x_244, 25);
x_277 = lean_ctor_get_uint8(x_244, sizeof(void*)*26 + 4);
lean_inc_ref(x_216);
x_356 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_356, 0, x_223);
lean_ctor_set(x_356, 1, x_216);
lean_ctor_set(x_356, 2, x_217);
lean_ctor_set_uint8(x_356, sizeof(void*)*3, x_214);
lean_ctor_set_uint8(x_356, sizeof(void*)*3 + 1, x_215);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_226, 6);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_225, 6);
x_359 = lean_ctor_get(x_358, 25);
if (lean_obj_tag(x_359) == 0)
{
x_298 = x_356;
x_299 = lean_box(0);
goto block_320;
}
else
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
x_361 = lean_unbox(x_360);
x_352 = x_361;
x_353 = x_356;
x_354 = lean_box(0);
goto block_355;
}
}
else
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_357, 0);
x_363 = lean_unbox(x_362);
x_352 = x_363;
x_353 = x_356;
x_354 = lean_box(0);
goto block_355;
}
}
else
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_276, 0);
x_365 = lean_unbox(x_364);
x_352 = x_365;
x_353 = x_356;
x_354 = lean_box(0);
goto block_355;
}
block_243:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_238);
x_240 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = l_Lake_CacheMap_insertCore(x_228, x_240, x_232);
x_242 = lean_st_ref_set(x_236, x_241);
lean_dec(x_236);
x_14 = x_230;
x_15 = x_235;
x_16 = x_237;
x_17 = x_234;
x_18 = x_231;
x_19 = lean_box(0);
goto block_23;
}
block_271:
{
if (lean_obj_tag(x_245) == 1)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; uint64_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_249 = lean_ctor_get(x_245, 0);
lean_inc(x_249);
lean_dec_ref(x_245);
x_250 = lean_st_ref_take(x_249);
x_251 = lean_ctor_get(x_246, 0);
x_252 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_252);
x_253 = lean_ctor_get_uint8(x_247, sizeof(void*)*3);
x_254 = lean_ctor_get_uint8(x_247, sizeof(void*)*3 + 1);
x_255 = lean_ctor_get(x_247, 1);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_247, 2);
lean_inc(x_256);
lean_dec_ref(x_247);
x_257 = lean_ctor_get_uint64(x_251, sizeof(void*)*1);
x_258 = lean_ctor_get(x_251, 0);
x_259 = lean_string_utf8_byte_size(x_258);
x_260 = lean_unsigned_to_nat(0u);
x_261 = lean_nat_dec_eq(x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = l_Lake_Hash_hex(x_257);
x_263 = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
x_264 = lean_string_append(x_262, x_263);
x_265 = lean_string_append(x_264, x_258);
x_230 = x_246;
x_231 = x_256;
x_232 = x_250;
x_233 = lean_box(0);
x_234 = x_254;
x_235 = x_252;
x_236 = x_249;
x_237 = x_253;
x_238 = x_255;
x_239 = x_265;
goto block_243;
}
else
{
lean_object* x_266; 
x_266 = l_Lake_Hash_hex(x_257);
x_230 = x_246;
x_231 = x_256;
x_232 = x_250;
x_233 = lean_box(0);
x_234 = x_254;
x_235 = x_252;
x_236 = x_249;
x_237 = x_253;
x_238 = x_255;
x_239 = x_266;
goto block_243;
}
}
else
{
lean_object* x_267; uint8_t x_268; uint8_t x_269; lean_object* x_270; 
lean_dec(x_245);
x_267 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_267);
x_268 = lean_ctor_get_uint8(x_247, sizeof(void*)*3);
x_269 = lean_ctor_get_uint8(x_247, sizeof(void*)*3 + 1);
x_270 = lean_ctor_get(x_247, 2);
lean_inc(x_270);
lean_dec_ref(x_247);
x_14 = x_246;
x_15 = x_267;
x_16 = x_268;
x_17 = x_269;
x_18 = x_270;
x_19 = lean_box(0);
goto block_23;
}
}
block_275:
{
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec_ref(x_272);
x_246 = x_273;
x_247 = x_274;
x_248 = lean_box(0);
goto block_271;
}
else
{
lean_dec(x_245);
return x_272;
}
}
block_291:
{
lean_object* x_281; 
lean_inc_ref(x_11);
lean_inc_ref(x_219);
lean_inc_ref(x_1);
lean_inc(x_224);
lean_inc_ref(x_227);
x_281 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_228, x_222, x_227, x_224, x_1, x_6, x_219, x_278, x_7, x_8, x_9, x_10, x_11, x_279);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 1)
{
lean_object* x_283; lean_object* x_284; 
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec_ref(x_281);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
lean_dec_ref(x_282);
x_246 = x_284;
x_247 = x_283;
x_248 = lean_box(0);
goto block_271;
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_282);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_dec_ref(x_281);
x_286 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_216, x_219, x_7, x_8, x_9, x_10, x_11, x_285);
lean_dec_ref(x_216);
x_272 = x_286;
goto block_275;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_245);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_287 = lean_ctor_get(x_281, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_281, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_289 = x_281;
} else {
 lean_dec_ref(x_281);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
block_297:
{
if (x_293 == 0)
{
lean_object* x_296; 
lean_dec(x_222);
x_296 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_216, x_219, x_7, x_8, x_9, x_10, x_11, x_294);
lean_dec_ref(x_216);
x_272 = x_296;
goto block_275;
}
else
{
x_278 = x_292;
x_279 = x_294;
x_280 = lean_box(0);
goto block_291;
}
}
block_320:
{
lean_object* x_300; 
lean_inc(x_222);
x_300 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_216, x_222, x_229, x_8, x_9, x_10, x_11, x_298);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_303 = 0;
x_304 = lean_unbox(x_301);
lean_dec(x_301);
x_305 = l_Lake_instDecidableEqOutputStatus(x_304, x_303);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec(x_222);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_306 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_302);
lean_dec_ref(x_11);
x_272 = x_306;
goto block_275;
}
else
{
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_226, 6);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_225, 6);
x_309 = lean_ctor_get(x_308, 25);
if (lean_obj_tag(x_309) == 0)
{
x_278 = x_305;
x_279 = x_302;
x_280 = lean_box(0);
goto block_291;
}
else
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_ctor_get(x_309, 0);
x_311 = lean_unbox(x_310);
x_292 = x_305;
x_293 = x_311;
x_294 = x_302;
x_295 = lean_box(0);
goto block_297;
}
}
else
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_307, 0);
x_313 = lean_unbox(x_312);
x_292 = x_305;
x_293 = x_313;
x_294 = x_302;
x_295 = lean_box(0);
goto block_297;
}
}
else
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_276, 0);
x_315 = lean_unbox(x_314);
x_292 = x_305;
x_293 = x_315;
x_294 = x_302;
x_295 = lean_box(0);
goto block_297;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_245);
lean_dec(x_222);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_316 = lean_ctor_get(x_300, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_300, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_318 = x_300;
} else {
 lean_dec_ref(x_300);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
block_351:
{
lean_object* x_324; 
lean_inc_ref(x_11);
lean_inc_ref(x_219);
lean_inc_ref(x_1);
lean_inc(x_224);
lean_inc_ref(x_227);
lean_inc(x_222);
x_324 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_228, x_222, x_227, x_224, x_1, x_6, x_219, x_323, x_7, x_8, x_9, x_10, x_11, x_321);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 1)
{
lean_object* x_326; lean_object* x_327; 
lean_dec_ref(x_227);
lean_dec(x_224);
lean_dec(x_222);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec_ref(x_324);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
lean_dec_ref(x_325);
x_246 = x_327;
x_247 = x_326;
x_248 = lean_box(0);
goto block_271;
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_325);
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec_ref(x_324);
x_329 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_216, x_222, x_229, x_8, x_9, x_10, x_11, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec_ref(x_329);
x_332 = 0;
x_333 = lean_unbox(x_330);
x_334 = l_Lake_instDecidableEqOutputStatus(x_333, x_332);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; lean_object* x_337; 
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_2);
x_335 = lean_box(0);
x_336 = lean_unbox(x_330);
lean_dec(x_330);
x_337 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_336, x_1, x_4, x_3, x_6, x_323, x_224, x_227, x_228, x_335, x_7, x_8, x_9, x_10, x_11, x_331);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_272 = x_337;
goto block_275;
}
else
{
lean_object* x_338; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_338 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_216, x_219, x_7, x_8, x_9, x_10, x_11, x_331);
lean_dec_ref(x_216);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_box(0);
x_341 = lean_unbox(x_330);
lean_dec(x_330);
x_342 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_341, x_1, x_4, x_3, x_6, x_323, x_224, x_227, x_228, x_340, x_7, x_8, x_9, x_10, x_11, x_339);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_272 = x_342;
goto block_275;
}
else
{
lean_dec(x_330);
lean_dec(x_245);
lean_dec_ref(x_227);
lean_dec(x_224);
lean_dec_ref(x_8);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_338;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_245);
lean_dec_ref(x_227);
lean_dec(x_224);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_343 = lean_ctor_get(x_329, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_329, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_345 = x_329;
} else {
 lean_dec_ref(x_329);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_245);
lean_dec_ref(x_227);
lean_dec(x_224);
lean_dec(x_222);
lean_dec_ref(x_8);
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_347 = lean_ctor_get(x_324, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_324, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_349 = x_324;
} else {
 lean_dec_ref(x_324);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
block_355:
{
if (x_352 == 0)
{
x_298 = x_353;
x_299 = lean_box(0);
goto block_320;
}
else
{
lean_inc_ref(x_227);
lean_inc(x_224);
if (x_5 == 0)
{
x_321 = x_353;
x_322 = lean_box(0);
x_323 = x_277;
goto block_351;
}
else
{
x_321 = x_353;
x_322 = lean_box(0);
x_323 = x_5;
goto block_351;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_220, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_220, 1);
lean_inc(x_367);
lean_dec_ref(x_220);
x_368 = lean_ctor_get(x_216, 2);
lean_inc_ref(x_216);
x_369 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_216);
lean_ctor_set(x_369, 2, x_217);
lean_ctor_set_uint8(x_369, sizeof(void*)*3, x_214);
lean_ctor_set_uint8(x_369, sizeof(void*)*3 + 1, x_215);
x_370 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_216, x_366, x_368, x_8, x_9, x_10, x_11, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec_ref(x_370);
x_373 = 0;
x_374 = lean_unbox(x_371);
lean_dec(x_371);
x_375 = l_Lake_instDecidableEqOutputStatus(x_374, x_373);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_376 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_372);
lean_dec_ref(x_11);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec_ref(x_376);
x_24 = x_377;
x_25 = x_378;
x_26 = lean_box(0);
goto block_38;
}
else
{
return x_376;
}
}
else
{
lean_object* x_379; 
x_379 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_216, x_219, x_7, x_8, x_9, x_10, x_11, x_372);
lean_dec_ref(x_216);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec_ref(x_379);
x_24 = x_380;
x_25 = x_381;
x_26 = lean_box(0);
goto block_38;
}
else
{
return x_379;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec_ref(x_219);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_382 = lean_ctor_get(x_370, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_370, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_384 = x_370;
} else {
 lean_dec_ref(x_370);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec_ref(x_219);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_386 = lean_ctor_get(x_220, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_220, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_388 = x_220;
} else {
 lean_dec_ref(x_220);
 x_388 = lean_box(0);
}
x_389 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_216);
lean_ctor_set(x_389, 2, x_217);
lean_ctor_set_uint8(x_389, sizeof(void*)*3, x_214);
lean_ctor_set_uint8(x_389, sizeof(void*)*3 + 1, x_215);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lake_Artifact_trace(x_14);
x_21 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
block_38:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
x_29 = l_Lake_Artifact_trace(x_24);
lean_ctor_set(x_25, 1, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get_uint8(x_25, sizeof(void*)*3);
x_33 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 1);
x_34 = lean_ctor_get(x_25, 2);
lean_inc(x_34);
lean_inc(x_31);
lean_dec(x_25);
x_35 = l_Lake_Artifact_trace(x_24);
x_36 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lake_BuildTrace_mix(x_17, x_15);
lean_ctor_set(x_14, 1, x_18);
x_19 = lean_apply_1(x_2, x_5);
x_20 = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
x_21 = 0;
x_22 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_19, x_4, x_20, x_21, x_21, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get(x_14, 1);
x_38 = lean_ctor_get(x_14, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_34);
lean_dec(x_14);
x_39 = l_Lake_BuildTrace_mix(x_37, x_15);
x_40 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*3 + 1, x_36);
x_41 = lean_apply_1(x_2, x_5);
x_42 = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
x_43 = 0;
x_44 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_41, x_4, x_42, x_43, x_43, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_48);
lean_dec(x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_10 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_10, sizeof(void*)*3, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_10);
x_20 = lean_array_push(x_10, x_18);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_22);
lean_dec(x_7);
lean_inc_ref(x_1);
x_27 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_22);
x_36 = lean_array_push(x_22, x_34);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_10 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_10, sizeof(void*)*3, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_10);
x_20 = lean_array_push(x_10, x_18);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_22);
lean_dec(x_7);
lean_inc_ref(x_1);
x_27 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_22);
x_36 = lean_array_push(x_22, x_34);
x_37 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget_borrowed(x_2, x_3);
x_17 = l_System_FilePath_isDir(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_1);
lean_inc(x_16);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; 
lean_inc(x_16);
x_20 = lean_array_push(x_5, x_16);
x_8 = x_20;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_21; 
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
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
static lean_object* _init_l_Lake_inputDir___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = l_System_FilePath_walkDir(x_1, x_2);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_49; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get_size(x_38);
x_54 = lean_obj_once(&l_Lake_inputDir___lam__1___closed__0, &l_Lake_inputDir___lam__1___closed__0_once, _init_l_Lake_inputDir___lam__1___closed__0);
x_55 = lean_nat_dec_lt(x_39, x_53);
if (x_55 == 0)
{
lean_dec(x_38);
lean_dec_ref(x_3);
x_40 = x_54;
x_41 = x_9;
x_42 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
if (x_55 == 0)
{
lean_dec(x_38);
lean_dec_ref(x_3);
x_40 = x_54;
x_41 = x_9;
x_42 = lean_box(0);
goto block_48;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_53);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_38, x_57, x_58, x_54, x_9);
lean_dec(x_38);
x_49 = x_59;
goto block_52;
}
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_53);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_38, x_60, x_61, x_54, x_9);
lean_dec(x_38);
x_49 = x_62;
goto block_52;
}
}
block_48:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_array_get_size(x_40);
x_44 = lean_nat_dec_eq(x_43, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_43, x_45);
x_47 = lean_nat_dec_le(x_39, x_46);
if (x_47 == 0)
{
lean_inc(x_46);
x_24 = x_43;
x_25 = lean_box(0);
x_26 = x_40;
x_27 = x_41;
x_28 = x_46;
x_29 = x_46;
goto block_31;
}
else
{
x_24 = x_43;
x_25 = lean_box(0);
x_26 = x_40;
x_27 = x_41;
x_28 = x_46;
x_29 = x_39;
goto block_31;
}
}
else
{
x_11 = lean_box(0);
x_12 = x_41;
x_13 = x_40;
goto block_15;
}
}
block_52:
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_40 = x_50;
x_41 = x_51;
x_42 = lean_box(0);
goto block_48;
}
else
{
return x_49;
}
}
}
else
{
uint8_t x_63; 
lean_inc(x_36);
lean_inc_ref(x_35);
lean_inc_ref(x_32);
lean_dec_ref(x_3);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_9, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_9, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_9, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
lean_dec_ref(x_37);
x_68 = lean_io_error_to_string(x_67);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_get_size(x_32);
x_72 = lean_array_push(x_32, x_70);
lean_ctor_set(x_9, 0, x_72);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
x_74 = lean_ctor_get(x_37, 0);
lean_inc(x_74);
lean_dec_ref(x_37);
x_75 = lean_io_error_to_string(x_74);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_get_size(x_32);
x_79 = lean_array_push(x_32, x_77);
x_80 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_36);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_33);
lean_ctor_set_uint8(x_80, sizeof(void*)*3 + 1, x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_23:
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_19, x_18, x_21);
lean_dec(x_21);
x_11 = lean_box(0);
x_12 = x_20;
x_13 = x_22;
goto block_15;
}
block_31:
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_29, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_inc(x_29);
x_16 = lean_box(0);
x_17 = x_24;
x_18 = x_29;
x_19 = x_26;
x_20 = x_27;
x_21 = x_29;
goto block_23;
}
else
{
x_16 = lean_box(0);
x_17 = x_24;
x_18 = x_29;
x_19 = x_26;
x_20 = x_27;
x_21 = x_28;
goto block_23;
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_Job_collectArray___redArg(x_15, x_2);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lake_Job_collectArray___redArg(x_17, x_2);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_10, 0, x_21);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get(x_10, 1);
x_29 = lean_ctor_get(x_10, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_25);
lean_dec(x_10);
x_30 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_27);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_27);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_15, 2);
lean_inc(x_21);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_22 = x_15;
} else {
 lean_dec_ref(x_15);
 x_22 = lean_box(0);
}
x_23 = l_Lake_platformTrace;
x_24 = l_Lake_BuildTrace_mix(x_20, x_23);
x_85 = l_Lake_Hash_nil;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_array_get_size(x_1);
x_88 = lean_nat_dec_lt(x_86, x_87);
if (x_88 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_25 = x_85;
goto block_84;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_87, x_87);
if (x_89 == 0)
{
if (x_88 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_25 = x_85;
goto block_84;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_87);
x_92 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_90, x_91, x_92);
x_94 = lean_unbox_uint64(x_93);
lean_dec(x_93);
x_25 = x_94;
goto block_84;
}
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; uint64_t x_99; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_87);
x_97 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_95, x_96, x_97);
x_99 = lean_unbox_uint64(x_98);
lean_dec(x_98);
x_25 = x_99;
goto block_84;
}
}
block_84:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_27 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(x_1);
x_28 = lean_array_to_list(x_1);
x_29 = l_List_toString___redArg(x_2, x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_26, x_30);
lean_dec_ref(x_30);
x_32 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_33 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_34 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_25);
x_35 = l_Lake_BuildTrace_mix(x_24, x_34);
if (lean_is_scalar(x_22)) {
 x_36 = lean_alloc_ctor(0, 3, 2);
} else {
 x_36 = x_22;
}
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_19);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_37 = lean_apply_7(x_3, x_10, x_11, x_12, x_13, x_14, x_36, lean_box(0));
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lake_BuildTrace_mix(x_41, x_39);
lean_ctor_set(x_38, 1, x_42);
x_43 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_44 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_44, 0, x_5);
lean_closure_set(x_44, 1, x_9);
lean_closure_set(x_44, 2, x_43);
lean_closure_set(x_44, 3, x_6);
x_45 = 0;
x_46 = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
x_47 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_44, x_45, x_46, x_45, x_45, x_10, x_11, x_12, x_13, x_14, x_38);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_50);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get_uint8(x_38, sizeof(void*)*3);
x_61 = lean_ctor_get_uint8(x_38, sizeof(void*)*3 + 1);
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_59);
lean_dec(x_38);
x_64 = l_Lake_BuildTrace_mix(x_62, x_39);
x_65 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*3 + 1, x_61);
x_66 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_67 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_67, 0, x_5);
lean_closure_set(x_67, 1, x_9);
lean_closure_set(x_67, 2, x_66);
lean_closure_set(x_67, 3, x_6);
x_68 = 0;
x_69 = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
x_70 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_67, x_68, x_69, x_68, x_68, x_10, x_11, x_12, x_13, x_14, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_74);
lean_dec(x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
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
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
return x_37;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_37, 0);
x_82 = lean_ctor_get(x_37, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_37);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
x_2 = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_20 = x_11;
} else {
 lean_dec_ref(x_11);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_21, 4);
lean_inc_ref(x_46);
x_22 = x_46;
goto block_45;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_5, 0);
lean_inc(x_47);
lean_dec_ref(x_5);
x_22 = x_47;
goto block_45;
}
block_45:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_21, 12);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_21, 16);
lean_inc_ref(x_24);
lean_dec_ref(x_21);
x_25 = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__2, &l_Lake_buildLeanO___lam__0___closed__2_once, _init_l_Lake_buildLeanO___lam__0___closed__2);
x_26 = lean_array_push(x_25, x_22);
x_27 = l_Array_append___redArg(x_26, x_24);
lean_dec_ref(x_24);
x_28 = l_Array_append___redArg(x_27, x_1);
x_29 = l_Array_append___redArg(x_28, x_2);
x_30 = l_Lake_compileO(x_3, x_4, x_29, x_23, x_15);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_20)) {
 x_33 = lean_alloc_ctor(0, 3, 2);
} else {
 x_33 = x_20;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_18);
lean_ctor_set(x_33, 2, x_19);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_33, sizeof(void*)*3 + 1, x_17);
lean_ctor_set(x_30, 1, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
if (lean_is_scalar(x_20)) {
 x_36 = lean_alloc_ctor(0, 3, 2);
} else {
 x_36 = x_20;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_19);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_17);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_20)) {
 x_40 = lean_alloc_ctor(0, 3, 2);
} else {
 x_40 = x_20;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_40, 2, x_19);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_40, sizeof(void*)*3 + 1, x_17);
lean_ctor_set(x_30, 1, x_40);
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
if (lean_is_scalar(x_20)) {
 x_43 = lean_alloc_ctor(0, 3, 2);
} else {
 x_43 = x_20;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_18);
lean_ctor_set(x_43, 2, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_16 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_11, 2);
lean_inc(x_17);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_18 = x_11;
} else {
 lean_dec_ref(x_11);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_5);
lean_closure_set(x_20, 4, x_4);
lean_inc_ref(x_19);
x_21 = l_Lake_BuildTrace_mix(x_16, x_19);
x_51 = l_Lake_Hash_nil;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get_size(x_2);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
x_22 = x_51;
goto block_50;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
if (x_54 == 0)
{
x_22 = x_51;
goto block_50;
}
else
{
size_t x_56; size_t x_57; uint64_t x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_53);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_56, x_57, x_51);
x_22 = x_58;
goto block_50;
}
}
else
{
size_t x_59; size_t x_60; uint64_t x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_59, x_60, x_51);
x_22 = x_61;
goto block_50;
}
}
block_50:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_23 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_24 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_25 = lean_array_to_list(x_2);
x_26 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec_ref(x_26);
x_28 = lean_string_append(x_23, x_27);
lean_dec_ref(x_27);
x_29 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_30 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_31 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_22);
x_32 = l_Lake_BuildTrace_mix(x_21, x_31);
x_33 = l_Lake_platformTrace;
x_34 = l_Lake_BuildTrace_mix(x_32, x_33);
if (lean_is_scalar(x_18)) {
 x_35 = lean_alloc_ctor(0, 3, 2);
} else {
 x_35 = x_18;
}
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_17);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_14);
lean_ctor_set_uint8(x_35, sizeof(void*)*3 + 1, x_15);
x_36 = 0;
x_37 = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
x_38 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_20, x_36, x_37, x_36, x_36, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_41);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = l_Lake_compileStaticLib(x_1, x_2, x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_9, 0, x_19);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_9, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_9, 0, x_24);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
lean_ctor_set(x_9, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_31 = lean_ctor_get(x_9, 1);
x_32 = lean_ctor_get(x_9, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_28);
lean_dec(x_9);
x_33 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_33);
lean_dec_ref(x_13);
x_34 = l_Lake_compileStaticLib(x_1, x_2, x_33, x_3, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_30);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_29);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_30);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
x_3 = lean_obj_once(&l_Lake_inputDir___lam__1___closed__0, &l_Lake_inputDir___lam__1___closed__0_once, _init_l_Lake_inputDir___lam__1___closed__0);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_string_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_8);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_nat_add(x_13, x_14);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_nat_add(x_13, x_14);
x_38 = lean_nat_add(x_37, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_31);
lean_ctor_set(x_43, 4, x_19);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_37, x_46);
lean_dec(x_46);
lean_dec(x_37);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_6);
lean_ctor_set(x_48, 3, x_7);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_13, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_39 = x_48;
x_40 = x_49;
x_41 = x_50;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_39 = x_48;
x_40 = x_49;
x_41 = x_51;
goto block_45;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_9);
x_55 = lean_nat_add(x_13, x_14);
x_56 = lean_nat_add(x_55, x_15);
lean_dec(x_15);
x_57 = lean_nat_add(x_55, x_27);
lean_dec(x_55);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_7);
lean_ctor_set(x_58, 4, x_18);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_7, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
lean_ctor_set(x_7, 4, x_19);
lean_ctor_set(x_7, 3, x_58);
lean_ctor_set(x_7, 2, x_17);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
else
{
lean_object* x_65; 
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_16);
lean_ctor_set(x_65, 2, x_17);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_19);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_12, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_12);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_12, 4);
x_69 = lean_ctor_get(x_12, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_12, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 2);
x_74 = lean_ctor_get(x_66, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
lean_ctor_set(x_66, 4, x_68);
lean_ctor_set(x_66, 3, x_68);
lean_ctor_set(x_66, 2, x_6);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 0, x_13);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_9;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_12);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_66, 1);
x_80 = lean_ctor_get(x_66, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_13);
lean_ctor_set(x_82, 1, x_5);
lean_ctor_set(x_82, 2, x_6);
lean_ctor_set(x_82, 3, x_68);
lean_ctor_set(x_82, 4, x_68);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_9;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_12);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_12, 4);
x_85 = lean_ctor_get(x_12, 1);
x_86 = lean_ctor_get(x_12, 2);
lean_inc(x_84);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_12);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 2);
lean_inc(x_88);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_89 = x_66;
} else {
 lean_dec_ref(x_66);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(3u);
lean_inc_n(x_84, 2);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_6);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_84);
lean_inc(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_84);
lean_ctor_set(x_92, 4, x_84);
if (lean_is_scalar(x_9)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_9;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_12, 4);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_12, 1);
x_97 = lean_ctor_get(x_12, 2);
x_98 = lean_ctor_get(x_12, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_12, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 0);
lean_dec(x_100);
x_101 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_12, 4, x_66);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_9;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_12);
lean_ctor_set(x_102, 4, x_94);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_12, 1);
x_104 = lean_ctor_get(x_12, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 3, x_66);
lean_ctor_set(x_106, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_9;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_94);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_94);
lean_ctor_set(x_109, 4, x_12);
return x_109;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_1);
lean_ctor_set(x_110, 2, x_2);
lean_ctor_set(x_110, 3, x_7);
lean_ctor_set(x_110, 4, x_8);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
x_111 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_7);
x_112 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_8, 0);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 4);
lean_inc(x_118);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_mul(x_119, x_113);
x_121 = lean_nat_dec_lt(x_120, x_114);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_122 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_123 = lean_nat_add(x_122, x_113);
lean_dec(x_122);
if (lean_is_scalar(x_9)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_9;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_111);
lean_ctor_set(x_124, 4, x_8);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
x_129 = lean_ctor_get(x_118, 2);
x_130 = lean_ctor_get(x_118, 3);
x_131 = lean_ctor_get(x_118, 4);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_mul(x_132, x_126);
x_134 = lean_nat_dec_lt(x_127, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_145; lean_object* x_146; 
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_137 = lean_nat_add(x_136, x_113);
lean_dec(x_136);
x_145 = lean_nat_add(x_112, x_126);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_144:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_nat_add(x_138, x_140);
lean_dec(x_140);
lean_dec(x_138);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
lean_ctor_set(x_142, 2, x_6);
lean_ctor_set(x_142, 3, x_131);
lean_ctor_set(x_142, 4, x_8);
if (lean_is_scalar(x_125)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_125;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set(x_143, 2, x_129);
lean_ctor_set(x_143, 3, x_139);
lean_ctor_set(x_143, 4, x_142);
return x_143;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set(x_148, 2, x_116);
lean_ctor_set(x_148, 3, x_117);
lean_ctor_set(x_148, 4, x_130);
x_149 = lean_nat_add(x_112, x_113);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_138 = x_149;
x_139 = x_148;
x_140 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_138 = x_149;
x_139 = x_148;
x_140 = x_151;
goto block_144;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_9);
x_155 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_156 = lean_nat_add(x_155, x_113);
lean_dec(x_155);
x_157 = lean_nat_add(x_112, x_113);
x_158 = lean_nat_add(x_157, x_127);
lean_dec(x_157);
lean_inc_ref(x_8);
if (lean_is_scalar(x_125)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_125;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_5);
lean_ctor_set(x_159, 2, x_6);
lean_ctor_set(x_159, 3, x_118);
lean_ctor_set(x_159, 4, x_8);
x_160 = !lean_is_exclusive(x_8);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_8, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_8, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_8, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_8, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_8, 0);
lean_dec(x_165);
lean_ctor_set(x_8, 4, x_159);
lean_ctor_set(x_8, 3, x_117);
lean_ctor_set(x_8, 2, x_116);
lean_ctor_set(x_8, 1, x_115);
lean_ctor_set(x_8, 0, x_156);
return x_8;
}
else
{
lean_object* x_166; 
lean_dec(x_8);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_115);
lean_ctor_set(x_166, 2, x_116);
lean_ctor_set(x_166, 3, x_117);
lean_ctor_set(x_166, 4, x_159);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_111, 3);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_111);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_111, 4);
x_170 = lean_ctor_get(x_111, 1);
x_171 = lean_ctor_get(x_111, 2);
x_172 = lean_ctor_get(x_111, 3);
lean_dec(x_172);
x_173 = lean_ctor_get(x_111, 0);
lean_dec(x_173);
x_174 = lean_unsigned_to_nat(3u);
lean_inc(x_169);
lean_ctor_set(x_111, 3, x_169);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_9;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_111);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_111, 4);
x_177 = lean_ctor_get(x_111, 1);
x_178 = lean_ctor_get(x_111, 2);
lean_inc(x_176);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_111);
x_179 = lean_unsigned_to_nat(3u);
lean_inc(x_176);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_112);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_176);
if (lean_is_scalar(x_9)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_9;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_111, 4);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_111);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_111, 1);
x_185 = lean_ctor_get(x_111, 2);
x_186 = lean_ctor_get(x_111, 4);
lean_dec(x_186);
x_187 = lean_ctor_get(x_111, 3);
lean_dec(x_187);
x_188 = lean_ctor_get(x_111, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_182, 1);
x_191 = lean_ctor_get(x_182, 2);
x_192 = lean_ctor_get(x_182, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_182, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_182, 0);
lean_dec(x_194);
x_195 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_182, 4, x_167);
lean_ctor_set(x_182, 3, x_167);
lean_ctor_set(x_182, 2, x_185);
lean_ctor_set(x_182, 1, x_184);
lean_ctor_set(x_182, 0, x_112);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_9;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_182);
lean_ctor_set(x_196, 4, x_111);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_182, 1);
x_198 = lean_ctor_get(x_182, 2);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_182);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_200, 0, x_112);
lean_ctor_set(x_200, 1, x_184);
lean_ctor_set(x_200, 2, x_185);
lean_ctor_set(x_200, 3, x_167);
lean_ctor_set(x_200, 4, x_167);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_9;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_111);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_ctor_get(x_111, 1);
x_203 = lean_ctor_get(x_111, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_111);
x_204 = lean_ctor_get(x_182, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 2);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_112);
lean_ctor_set(x_208, 1, x_202);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_167);
lean_ctor_set(x_208, 4, x_167);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_112);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_167);
lean_ctor_set(x_209, 4, x_167);
if (lean_is_scalar(x_9)) {
 x_210 = lean_alloc_ctor(0, 5, 0);
} else {
 x_210 = x_9;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_208);
lean_ctor_set(x_210, 4, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_212 = x_9;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_5);
lean_ctor_set(x_212, 2, x_6);
lean_ctor_set(x_212, 3, x_111);
lean_ctor_set(x_212, 4, x_182);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_1);
lean_ctor_set(x_214, 2, x_2);
lean_ctor_set(x_214, 3, x_3);
lean_ctor_set(x_214, 4, x_3);
return x_214;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
x_8 = lean_string_append(x_7, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
x_13 = lean_string_append(x_12, x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0));
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
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1, &l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_once, _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1);
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_7; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1, &l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_once, _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1);
x_38 = lean_array_get_size(x_1);
x_39 = lean_nat_dec_lt(x_36, x_38);
if (x_39 == 0)
{
x_4 = x_37;
goto block_6;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2, &l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_once, _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2);
x_41 = lean_nat_dec_le(x_38, x_38);
if (x_41 == 0)
{
if (x_39 == 0)
{
x_4 = x_37;
goto block_6;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_38);
x_44 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_42, x_43, x_40);
x_7 = x_44;
goto block_35;
}
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_38);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_45, x_46, x_40);
x_7 = x_47;
goto block_35;
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
block_35:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
x_12 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_8);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_10);
x_17 = lean_array_push(x_10, x_15);
lean_ctor_set(x_2, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_19);
lean_dec(x_2);
x_24 = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
x_25 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_8);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_19);
x_30 = lean_array_push(x_19, x_28);
x_31 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec_ref(x_7);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_4 = x_34;
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_17 = l_Array_append___redArg(x_16, x_2);
x_18 = l_Array_append___redArg(x_17, x_3);
x_19 = l_Lake_compileSharedLib(x_4, x_18, x_5, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_12, 0, x_21);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_12, 0, x_26);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_32 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_33 = lean_ctor_get(x_12, 1);
x_34 = lean_ctor_get(x_12, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_30);
lean_dec(x_12);
x_35 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_36 = l_Array_append___redArg(x_35, x_2);
x_37 = l_Array_append___redArg(x_36, x_3);
x_38 = l_Lake_compileSharedLib(x_4, x_37, x_5, x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_42, 2, x_34);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*3 + 1, x_32);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_31);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 1, x_32);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
return x_48;
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
uint8_t x_18; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
uint64_t x_16; uint64_t x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = l_Lake_Hash_nil;
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_array_get_size(x_1);
x_138 = lean_nat_dec_lt(x_136, x_137);
if (x_138 == 0)
{
x_16 = x_135;
goto block_134;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_137, x_137);
if (x_139 == 0)
{
if (x_138 == 0)
{
x_16 = x_135;
goto block_134;
}
else
{
size_t x_140; size_t x_141; uint64_t x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_137);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_140, x_141, x_135);
x_16 = x_142;
goto block_134;
}
}
else
{
size_t x_143; size_t x_144; uint64_t x_145; 
x_143 = 0;
x_144 = lean_usize_of_nat(x_137);
x_145 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_143, x_144, x_135);
x_16 = x_145;
goto block_134;
}
}
block_134:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_21 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_22 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_23 = lean_array_to_list(x_1);
x_24 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_21, x_25);
lean_dec_ref(x_25);
x_27 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_28 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint64(x_28, sizeof(void*)*3, x_16);
x_29 = l_Lake_BuildTrace_mix(x_18, x_28);
x_30 = l_Lake_platformTrace;
x_31 = l_Lake_BuildTrace_mix(x_29, x_30);
lean_ctor_set(x_14, 1, x_31);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_32 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_box(x_3);
lean_inc_ref(x_8);
x_38 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_19);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_8);
x_39 = l_Lake_BuildTrace_mix(x_36, x_34);
lean_ctor_set(x_33, 1, x_39);
x_40 = 1;
x_41 = 0;
x_42 = l_Lake_sharedLibExt;
x_43 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_38, x_41, x_42, x_40, x_41, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_8);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_7);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_8);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
x_59 = lean_ctor_get_uint8(x_33, sizeof(void*)*3 + 1);
x_60 = lean_ctor_get(x_33, 1);
x_61 = lean_ctor_get(x_33, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_57);
lean_dec(x_33);
x_62 = lean_box(x_3);
lean_inc_ref(x_8);
x_63 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_63, 0, x_62);
lean_closure_set(x_63, 1, x_19);
lean_closure_set(x_63, 2, x_4);
lean_closure_set(x_63, 3, x_8);
x_64 = l_Lake_BuildTrace_mix(x_60, x_34);
x_65 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_58);
lean_ctor_set_uint8(x_65, sizeof(void*)*3 + 1, x_59);
x_66 = 1;
x_67 = 0;
x_68 = l_Lake_sharedLibExt;
x_69 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_63, x_67, x_68, x_66, x_67, x_9, x_10, x_11, x_12, x_13, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_6);
lean_ctor_set(x_74, 2, x_8);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_80 = !lean_is_exclusive(x_32);
if (x_80 == 0)
{
return x_32;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_32, 0);
x_82 = lean_ctor_get(x_32, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_32);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_84 = lean_ctor_get(x_14, 0);
x_85 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_86 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_87 = lean_ctor_get(x_14, 1);
x_88 = lean_ctor_get(x_14, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_84);
lean_dec(x_14);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_91 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_92 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_93 = lean_array_to_list(x_1);
x_94 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_93);
lean_dec(x_93);
x_95 = lean_string_append(x_92, x_94);
lean_dec_ref(x_94);
x_96 = lean_string_append(x_91, x_95);
lean_dec_ref(x_95);
x_97 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_98 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set_uint64(x_98, sizeof(void*)*3, x_16);
x_99 = l_Lake_BuildTrace_mix(x_87, x_98);
x_100 = l_Lake_platformTrace;
x_101 = l_Lake_BuildTrace_mix(x_99, x_100);
x_102 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_102, 0, x_84);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_88);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_85);
lean_ctor_set_uint8(x_102, sizeof(void*)*3 + 1, x_86);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_103 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_102, lean_box(0));
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get_uint8(x_104, sizeof(void*)*3);
x_108 = lean_ctor_get_uint8(x_104, sizeof(void*)*3 + 1);
x_109 = lean_ctor_get(x_104, 1);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_104, 2);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
 x_111 = lean_box(0);
}
x_112 = lean_box(x_3);
lean_inc_ref(x_8);
x_113 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_113, 0, x_112);
lean_closure_set(x_113, 1, x_89);
lean_closure_set(x_113, 2, x_4);
lean_closure_set(x_113, 3, x_8);
x_114 = l_Lake_BuildTrace_mix(x_109, x_105);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 3, 2);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set_uint8(x_115, sizeof(void*)*3, x_107);
lean_ctor_set_uint8(x_115, sizeof(void*)*3 + 1, x_108);
x_116 = 1;
x_117 = 0;
x_118 = l_Lake_sharedLibExt;
x_119 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_113, x_117, x_118, x_116, x_117, x_9, x_10, x_11, x_12, x_13, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_120, 1);
lean_inc_ref(x_123);
lean_dec(x_120);
x_124 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_6);
lean_ctor_set(x_124, 2, x_8);
lean_ctor_set_uint8(x_124, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_128 = x_119;
} else {
 lean_dec_ref(x_119);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_130 = lean_ctor_get(x_103, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_103, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_132 = x_103;
} else {
 lean_dec_ref(x_103);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
x_2 = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
lean_object* x_67; 
x_67 = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1, &l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_once, _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1);
x_17 = x_67;
x_18 = x_12;
x_19 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_68; 
x_68 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_6, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_17 = x_69;
x_18 = x_70;
x_19 = lean_box(0);
goto block_66;
}
else
{
uint8_t x_71; 
lean_dec_ref(x_16);
lean_dec_ref(x_4);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
block_66:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 12);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 18);
lean_inc_ref(x_22);
lean_dec_ref(x_16);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_26 = l_Array_append___redArg(x_25, x_2);
x_27 = l_Array_append___redArg(x_26, x_3);
x_28 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
x_29 = lean_array_push(x_28, x_20);
x_30 = l_Array_append___redArg(x_27, x_29);
lean_dec_ref(x_29);
x_31 = l_Array_append___redArg(x_30, x_22);
lean_dec_ref(x_22);
x_32 = l_Lake_compileSharedLib(x_4, x_31, x_21, x_24);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_34);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_18);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_39);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_18);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_45 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 1);
x_46 = lean_ctor_get(x_18, 1);
x_47 = lean_ctor_get(x_18, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_43);
lean_dec(x_18);
x_48 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_49 = l_Array_append___redArg(x_48, x_2);
x_50 = l_Array_append___redArg(x_49, x_3);
x_51 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
x_52 = lean_array_push(x_51, x_20);
x_53 = l_Array_append___redArg(x_50, x_52);
lean_dec_ref(x_52);
x_54 = l_Array_append___redArg(x_53, x_22);
lean_dec_ref(x_22);
x_55 = l_Lake_compileSharedLib(x_4, x_54, x_21, x_43);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_47);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*3 + 1, x_45);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_46);
lean_ctor_set(x_64, 2, x_47);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_64, sizeof(void*)*3 + 1, x_45);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_19 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_14, 2);
lean_inc(x_20);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_21 = x_14;
} else {
 lean_dec_ref(x_14);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_13, 2);
x_23 = lean_box(x_5);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_24 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_23);
lean_closure_set(x_24, 5, x_8);
lean_inc_ref(x_22);
x_25 = l_Lake_BuildTrace_mix(x_19, x_22);
x_58 = l_Lake_Hash_nil;
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_3);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
x_26 = x_58;
goto block_57;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_60, x_60);
if (x_62 == 0)
{
if (x_61 == 0)
{
x_26 = x_58;
goto block_57;
}
else
{
size_t x_63; size_t x_64; uint64_t x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_60);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_63, x_64, x_58);
x_26 = x_65;
goto block_57;
}
}
else
{
size_t x_66; size_t x_67; uint64_t x_68; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_60);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_66, x_67, x_58);
x_26 = x_68;
goto block_57;
}
}
block_57:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_27 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_28 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_29 = lean_array_to_list(x_3);
x_30 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_29);
lean_dec(x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec_ref(x_30);
x_32 = lean_string_append(x_27, x_31);
lean_dec_ref(x_31);
x_33 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_34 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_35 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint64(x_35, sizeof(void*)*3, x_26);
x_36 = l_Lake_BuildTrace_mix(x_25, x_35);
x_37 = l_Lake_platformTrace;
x_38 = l_Lake_BuildTrace_mix(x_36, x_37);
if (lean_is_scalar(x_21)) {
 x_39 = lean_alloc_ctor(0, 3, 2);
} else {
 x_39 = x_21;
}
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_18);
x_40 = 0;
x_41 = l_Lake_sharedLibExt;
x_42 = 1;
x_43 = l_Lake_buildArtifactUnlessUpToDate(x_4, x_24, x_40, x_41, x_42, x_40, x_9, x_10, x_11, x_12, x_13, x_39);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_8);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_7);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_8);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_21 = lean_ctor_get(x_17, 12);
lean_inc_ref(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_19);
lean_dec(x_19);
x_25 = l_Array_append___redArg(x_24, x_3);
x_26 = l_Array_append___redArg(x_25, x_4);
x_27 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(x_20);
x_28 = lean_array_push(x_27, x_20);
x_29 = l_Array_append___redArg(x_26, x_28);
lean_dec_ref(x_28);
x_30 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_17);
lean_dec_ref(x_17);
x_31 = l_Array_append___redArg(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l_Lake_compileExe(x_6, x_31, x_21, x_23);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_34);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_18);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_39);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_18);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_45 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 1);
x_46 = lean_ctor_get(x_18, 1);
x_47 = lean_ctor_get(x_18, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_43);
lean_dec(x_18);
x_48 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_19);
lean_dec(x_19);
x_49 = l_Array_append___redArg(x_48, x_3);
x_50 = l_Array_append___redArg(x_49, x_4);
x_51 = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(x_20);
x_52 = lean_array_push(x_51, x_20);
x_53 = l_Array_append___redArg(x_50, x_52);
lean_dec_ref(x_52);
x_54 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_17);
lean_dec_ref(x_17);
x_55 = l_Array_append___redArg(x_53, x_54);
lean_dec_ref(x_54);
x_56 = l_Lake_compileExe(x_6, x_55, x_21, x_43);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_60, sizeof(void*)*3 + 1, x_45);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_46);
lean_ctor_set(x_65, 2, x_47);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_65, sizeof(void*)*3 + 1, x_45);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
x_67 = !lean_is_exclusive(x_14);
if (x_67 == 0)
{
return x_14;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_14, 0);
x_69 = lean_ctor_get(x_14, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_14);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
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
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_19 = x_12;
} else {
 lean_dec_ref(x_12);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_11, 2);
x_21 = lean_box(x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_22 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_21);
lean_closure_set(x_22, 5, x_5);
lean_inc_ref(x_20);
x_23 = l_Lake_BuildTrace_mix(x_17, x_20);
x_54 = l_Lake_Hash_nil;
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_3);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
x_24 = x_54;
goto block_53;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_56, x_56);
if (x_58 == 0)
{
if (x_57 == 0)
{
x_24 = x_54;
goto block_53;
}
else
{
size_t x_59; size_t x_60; uint64_t x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_56);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_59, x_60, x_54);
x_24 = x_61;
goto block_53;
}
}
else
{
size_t x_62; size_t x_63; uint64_t x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_56);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_62, x_63, x_54);
x_24 = x_64;
goto block_53;
}
}
block_53:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_25 = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
x_26 = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
x_27 = lean_array_to_list(x_3);
x_28 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = lean_string_append(x_25, x_29);
lean_dec_ref(x_29);
x_31 = lean_obj_once(&l_Lake_platformTrace___closed__2, &l_Lake_platformTrace___closed__2_once, _init_l_Lake_platformTrace___closed__2);
x_32 = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
x_33 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_24);
x_34 = l_Lake_BuildTrace_mix(x_23, x_33);
x_35 = l_Lake_platformTrace;
x_36 = l_Lake_BuildTrace_mix(x_34, x_35);
if (lean_is_scalar(x_19)) {
 x_37 = lean_alloc_ctor(0, 3, 2);
} else {
 x_37 = x_19;
}
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_18);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_16);
x_38 = 0;
x_39 = l_System_FilePath_exeExtension;
x_40 = 1;
x_41 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_22, x_38, x_39, x_40, x_40, x_7, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_44);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
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
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
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
#ifdef __cplusplus
}
#endif
