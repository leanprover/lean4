// Lean compiler output
// Module: Lean.Linter.InternalModule
// Imports: public import Lean.Linter.Basic public import Lean.Linter.Util public import Lean.PrivateName
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Linter_getNewDecls(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "coreInternal"};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "internalModule"};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 202, 150, 38, 196, 187, 132, 57)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(79, 143, 209, 6, 103, 6, 164, 164)}};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 138, .m_capacity = 138, .m_length = 137, .m_data = "enable the `internalModule` linter, which warns when a module considered \"internal\" declares a declaration that is not itself \"internal\"."};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 14, 14, 18, 112, 30, 27, 197)}};
static const lean_ctor_object l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 241, 232, 48, 133, 28, 88, 250)}};
static const lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_coreInternal_internalModule;
static const lean_string_object l_Lean_Linter_InternalModule_internalNameComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Linter_InternalModule_internalNameComponents___closed__0 = (const lean_object*)&l_Lean_Linter_InternalModule_internalNameComponents___closed__0_value;
static const lean_array_object l_Lean_Linter_InternalModule_internalNameComponents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lean_Linter_InternalModule_internalNameComponents___closed__0_value)}};
static const lean_object* l_Lean_Linter_InternalModule_internalNameComponents___closed__1 = (const lean_object*)&l_Lean_Linter_InternalModule_internalNameComponents___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_InternalModule_internalNameComponents = (const lean_object*)&l_Lean_Linter_InternalModule_internalNameComponents___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_hasInternalNameComponent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_hasInternalNameComponent___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__0 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__0_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Omega"};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__1 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__1_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2_value_aux_0),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 30, 205, 200, 94, 55, 22, 174)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__3 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__3_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4_value_aux_0),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 19, 144, 30, 69, 164, 148, 125)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__5 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__5_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__6 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__6_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__6_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__7 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__7_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "IMLinterTest"};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__8 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__8_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__8_value),LEAN_SCALAR_PTR_LITERAL(35, 25, 106, 152, 127, 213, 122, 40)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__9 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__9_value;
static const lean_array_object l_Lean_Linter_InternalModule_internalModulePrefixes___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__2_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__4_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__5_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__7_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__9_value)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes___closed__10 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_InternalModule_internalModulePrefixes = (const lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__10_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalModule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_InternalModule_isInternalModule___closed__0;
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalModule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Linter_InternalModule_isInternalModule___closed__1;
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalModule___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Linter_InternalModule_isInternalModule___closed__2;
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_isInternalModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_isInternalModule___boxed(lean_object*);
static const lean_array_object l_Lean_Linter_InternalModule_internalDeclNamespaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__5_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModulePrefixes___closed__7_value)}};
static const lean_object* l_Lean_Linter_InternalModule_internalDeclNamespaces___closed__0 = (const lean_object*)&l_Lean_Linter_InternalModule_internalDeclNamespaces___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_InternalModule_internalDeclNamespaces = (const lean_object*)&l_Lean_Linter_InternalModule_internalDeclNamespaces___closed__0_value;
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_InternalModule_isInternalDecl___closed__0;
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Linter_InternalModule_isInternalDecl___closed__1;
static lean_once_cell_t l_Lean_Linter_InternalModule_isInternalDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Linter_InternalModule_isInternalDecl___closed__2;
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_isInternalDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_isInternalDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "` is a non-internal declaration in the internal module `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 445, .m_capacity = 445, .m_length = 444, .m_data = "`; declarations in internal modules should themselves be internal.\n\nMake the declaration private, or put it into an internal namespace, or, if the declaration is supposed to be part of the standard library, move it into a file that is part of the standard library.\n\nFor core-specific helper functions about basic types, recall that after `open Lean`, a declaration like `Lean.List.foo` will be available for generalized field notation on lists."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__0 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__1 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalModule"};
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__2 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internalModuleLinter"};
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__3 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(112, 45, 25, 75, 167, 215, 136, 201)}};
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(206, 74, 95, 134, 69, 21, 65, 207)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__4 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__1_value),((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__5 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0(lean_object* v_a_68_, lean_object* v_as_69_, size_t v_i_70_, size_t v_stop_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_eq(v_i_70_, v_stop_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_array_uget_borrowed(v_as_69_, v_i_70_);
v___x_74_ = lean_string_dec_eq(v_a_68_, v___x_73_);
if (v___x_74_ == 0)
{
size_t v___x_75_; size_t v___x_76_; 
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_add(v_i_70_, v___x_75_);
v_i_70_ = v___x_76_;
goto _start;
}
else
{
return v___x_74_;
}
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0___boxed(lean_object* v_a_79_, lean_object* v_as_80_, lean_object* v_i_81_, lean_object* v_stop_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_82_);
lean_dec(v_stop_82_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0(v_a_79_, v_as_80_, v_i_boxed_83_, v_stop_boxed_84_);
lean_dec_ref(v_as_80_);
lean_dec_ref(v_a_79_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0(lean_object* v_as_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_array_get_size(v_as_87_);
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
size_t v___x_92_; size_t v___x_93_; uint8_t v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_90_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0_spec__0(v_a_88_, v_as_87_, v___x_92_, v___x_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0___boxed(lean_object* v_as_95_, lean_object* v_a_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0(v_as_95_, v_a_96_);
lean_dec_ref(v_a_96_);
lean_dec_ref(v_as_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_hasInternalNameComponent(lean_object* v_x_99_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 0:
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
case 1:
{
lean_object* v_pre_101_; lean_object* v_str_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_pre_101_ = lean_ctor_get(v_x_99_, 0);
v_str_102_ = lean_ctor_get(v_x_99_, 1);
v___x_103_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalNameComponents));
v___x_104_ = l_Array_contains___at___00Lean_Linter_InternalModule_hasInternalNameComponent_spec__0(v___x_103_, v_str_102_);
if (v___x_104_ == 0)
{
v_x_99_ = v_pre_101_;
goto _start;
}
else
{
return v___x_104_;
}
}
default: 
{
lean_object* v_pre_106_; 
v_pre_106_ = lean_ctor_get(v_x_99_, 0);
v_x_99_ = v_pre_106_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_hasInternalNameComponent___boxed(lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_Linter_InternalModule_hasInternalNameComponent(v_x_108_);
lean_dec(v_x_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(lean_object* v_mod_141_, lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_array_uget_borrowed(v_as_142_, v_i_143_);
v___x_147_ = l_Lean_Name_isPrefixOf(v___x_146_, v_mod_141_);
if (v___x_147_ == 0)
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_143_, v___x_148_);
v_i_143_ = v___x_149_;
goto _start;
}
else
{
return v___x_147_;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0___boxed(lean_object* v_mod_152_, lean_object* v_as_153_, lean_object* v_i_154_, lean_object* v_stop_155_){
_start:
{
size_t v_i_boxed_156_; size_t v_stop_boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_i_boxed_156_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_stop_boxed_157_ = lean_unbox_usize(v_stop_155_);
lean_dec(v_stop_155_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(v_mod_152_, v_as_153_, v_i_boxed_156_, v_stop_boxed_157_);
lean_dec_ref(v_as_153_);
lean_dec(v_mod_152_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
static lean_object* _init_l_Lean_Linter_InternalModule_isInternalModule___closed__0(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModulePrefixes));
v___x_161_ = lean_array_get_size(v___x_160_);
return v___x_161_;
}
}
static uint8_t _init_l_Lean_Linter_InternalModule_isInternalModule___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = lean_obj_once(&l_Lean_Linter_InternalModule_isInternalModule___closed__0, &l_Lean_Linter_InternalModule_isInternalModule___closed__0_once, _init_l_Lean_Linter_InternalModule_isInternalModule___closed__0);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_nat_dec_lt(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static size_t _init_l_Lean_Linter_InternalModule_isInternalModule___closed__2(void){
_start:
{
lean_object* v___x_165_; size_t v___x_166_; 
v___x_165_ = lean_obj_once(&l_Lean_Linter_InternalModule_isInternalModule___closed__0, &l_Lean_Linter_InternalModule_isInternalModule___closed__0_once, _init_l_Lean_Linter_InternalModule_isInternalModule___closed__0);
v___x_166_ = lean_usize_of_nat(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_isInternalModule(lean_object* v_mod_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Linter_InternalModule_hasInternalNameComponent(v_mod_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModulePrefixes));
v___x_170_ = lean_uint8_once(&l_Lean_Linter_InternalModule_isInternalModule___closed__1, &l_Lean_Linter_InternalModule_isInternalModule___closed__1_once, _init_l_Lean_Linter_InternalModule_isInternalModule___closed__1);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
size_t v___x_171_; size_t v___x_172_; uint8_t v___x_173_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_once(&l_Lean_Linter_InternalModule_isInternalModule___closed__2, &l_Lean_Linter_InternalModule_isInternalModule___closed__2_once, _init_l_Lean_Linter_InternalModule_isInternalModule___closed__2);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(v_mod_167_, v___x_169_, v___x_171_, v___x_172_);
return v___x_173_;
}
}
}
else
{
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_isInternalModule___boxed(lean_object* v_mod_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Linter_InternalModule_isInternalModule(v_mod_174_);
lean_dec(v_mod_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
static lean_object* _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__0(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalDeclNamespaces));
v___x_185_ = lean_array_get_size(v___x_184_);
return v___x_185_;
}
}
static uint8_t _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Linter_InternalModule_isInternalDecl___closed__0, &l_Lean_Linter_InternalModule_isInternalDecl___closed__0_once, _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__0);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_nat_dec_lt(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static size_t _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__2(void){
_start:
{
lean_object* v___x_189_; size_t v___x_190_; 
v___x_189_ = lean_obj_once(&l_Lean_Linter_InternalModule_isInternalDecl___closed__0, &l_Lean_Linter_InternalModule_isInternalDecl___closed__0_once, _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__0);
v___x_190_ = lean_usize_of_nat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_InternalModule_isInternalDecl(lean_object* v_declName_191_){
_start:
{
uint8_t v___y_193_; uint8_t v___x_195_; 
v___x_195_ = l_Lean_isPrivateName(v_declName_191_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalDeclNamespaces));
v___x_197_ = lean_uint8_once(&l_Lean_Linter_InternalModule_isInternalDecl___closed__1, &l_Lean_Linter_InternalModule_isInternalDecl___closed__1_once, _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__1);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = l_Lean_Linter_InternalModule_hasInternalNameComponent(v_declName_191_);
return v___x_198_;
}
else
{
if (v___x_197_ == 0)
{
uint8_t v___x_199_; 
v___x_199_ = l_Lean_Linter_InternalModule_hasInternalNameComponent(v_declName_191_);
return v___x_199_;
}
else
{
size_t v___x_200_; size_t v___x_201_; uint8_t v___x_202_; 
v___x_200_ = ((size_t)0ULL);
v___x_201_ = lean_usize_once(&l_Lean_Linter_InternalModule_isInternalDecl___closed__2, &l_Lean_Linter_InternalModule_isInternalDecl___closed__2_once, _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__2);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(v_declName_191_, v___x_196_, v___x_200_, v___x_201_);
v___y_193_ = v___x_202_;
goto v___jp_192_;
}
}
}
else
{
v___y_193_ = v___x_195_;
goto v___jp_192_;
}
v___jp_192_:
{
if (v___y_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_Linter_InternalModule_hasInternalNameComponent(v_declName_191_);
return v___x_194_;
}
else
{
return v___y_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_isInternalDecl___boxed(lean_object* v_declName_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lean_Linter_InternalModule_isInternalDecl(v_declName_203_);
lean_dec(v_declName_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_infoState_209_; lean_object* v_trees_210_; lean_object* v___x_211_; 
v___x_208_ = lean_st_ref_get(v___y_206_);
v_infoState_209_ = lean_ctor_get(v___x_208_, 8);
lean_inc_ref(v_infoState_209_);
lean_dec(v___x_208_);
v_trees_210_ = lean_ctor_get(v_infoState_209_, 2);
lean_inc_ref(v_trees_210_);
lean_dec_ref(v_infoState_209_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_trees_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___y_212_);
lean_dec(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___y_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_222_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_223_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_226_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_ctor_set(v___x_229_, 3, v___x_228_);
lean_ctor_set(v___x_229_, 4, v___x_227_);
lean_ctor_set(v___x_229_, 5, v___x_227_);
lean_ctor_set(v___x_229_, 6, v___x_227_);
lean_ctor_set(v___x_229_, 7, v___x_227_);
lean_ctor_set(v___x_229_, 8, v___x_227_);
lean_ctor_set(v___x_229_, 9, v___x_227_);
lean_ctor_set(v___x_229_, 10, v___x_227_);
lean_ctor_set(v___x_229_, 11, v___x_226_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(32u);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_233_ = ((size_t)5ULL);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_unsigned_to_nat(32u);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
v___x_237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__3);
v___x_238_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_234_);
lean_ctor_set(v___x_238_, 3, v___x_234_);
lean_ctor_set_usize(v___x_238_, 4, v___x_233_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_239_ = lean_box(1);
v___x_240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__4);
v___x_241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__1);
v___x_242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
lean_ctor_set(v___x_242_, 2, v___x_239_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_msgData_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_env_247_; uint8_t v___x_248_; lean_object* v_env_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_scopes_252_; lean_object* v___x_253_; lean_object* v_opts_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_246_ = lean_st_ref_get(v___y_244_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_ref(v_env_247_);
lean_dec(v___x_246_);
v___x_248_ = 0;
v_env_249_ = l_Lean_Environment_setRecordingDeps(v_env_247_, v___x_248_);
v___x_250_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_251_ = lean_st_ref_get(v___y_244_);
v_scopes_252_ = lean_ctor_get(v___x_251_, 2);
lean_inc(v_scopes_252_);
lean_dec(v___x_251_);
v___x_253_ = l_List_head_x21___redArg(v___x_250_, v_scopes_252_);
lean_dec(v_scopes_252_);
v_opts_254_ = lean_ctor_get(v___x_253_, 1);
lean_inc_ref(v_opts_254_);
lean_dec(v___x_253_);
v___x_255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__2);
v___x_256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___closed__5);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v_env_249_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_ctor_set(v___x_257_, 3, v_opts_254_);
v___x_258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_msgData_243_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg(v_msgData_260_, v___y_261_);
lean_dec(v___y_261_);
return v_res_263_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_265_, uint8_t v___y_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 1)
{
lean_object* v_pre_268_; 
v_pre_268_ = lean_ctor_get(v_x_267_, 0);
if (lean_obj_tag(v_pre_268_) == 0)
{
lean_object* v_str_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_str_269_ = lean_ctor_get(v_x_267_, 1);
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___closed__0));
v___x_271_ = lean_string_dec_eq(v_str_269_, v___x_270_);
if (v___x_271_ == 0)
{
return v___x_271_;
}
else
{
return v_suppressElabErrors_265_;
}
}
else
{
return v___y_266_;
}
}
else
{
return v___y_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_272_, lean_object* v___y_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_suppressElabErrors_boxed_275_; uint8_t v___y_8025__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_suppressElabErrors_boxed_275_ = lean_unbox(v_suppressElabErrors_272_);
v___y_8025__boxed_276_ = lean_unbox(v___y_273_);
v_res_277_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_275_, v___y_8025__boxed_276_, v_x_274_);
lean_dec(v_x_274_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8(lean_object* v_opts_279_, lean_object* v_opt_280_){
_start:
{
lean_object* v_name_281_; lean_object* v_defValue_282_; lean_object* v_map_283_; lean_object* v___x_284_; 
v_name_281_ = lean_ctor_get(v_opt_280_, 0);
v_defValue_282_ = lean_ctor_get(v_opt_280_, 1);
v_map_283_ = lean_ctor_get(v_opts_279_, 0);
v___x_284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_283_, v_name_281_);
if (lean_obj_tag(v___x_284_) == 0)
{
uint8_t v___x_285_; 
v___x_285_ = lean_unbox(v_defValue_282_);
return v___x_285_;
}
else
{
lean_object* v_val_286_; 
v_val_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_284_, 1);
if (lean_obj_tag(v_val_286_) == 1)
{
uint8_t v_v_287_; 
v_v_287_ = lean_ctor_get_uint8(v_val_286_, 0);
lean_dec_ref_known(v_val_286_, 0);
return v_v_287_;
}
else
{
uint8_t v___x_288_; 
lean_dec(v_val_286_);
v___x_288_ = lean_unbox(v_defValue_282_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_opts_289_, lean_object* v_opt_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8(v_opts_289_, v_opt_290_);
lean_dec_ref(v_opt_290_);
lean_dec_ref(v_opts_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4(lean_object* v_ref_294_, lean_object* v_msgData_295_, uint8_t v_severity_296_, uint8_t v_isSilent_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; lean_object* v___y_309_; uint8_t v___y_367_; lean_object* v___y_368_; uint8_t v___y_369_; uint8_t v___y_370_; lean_object* v___y_371_; uint8_t v___y_395_; lean_object* v___y_396_; uint8_t v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_403_; uint8_t v___y_404_; uint8_t v___y_405_; uint8_t v___x_420_; uint8_t v___y_422_; uint8_t v___y_423_; uint8_t v___y_424_; uint8_t v___y_426_; uint8_t v___x_438_; 
v___x_420_ = 2;
v___x_438_ = l_Lean_instBEqMessageSeverity_beq(v_severity_296_, v___x_420_);
if (v___x_438_ == 0)
{
v___y_426_ = v___x_438_;
goto v___jp_425_;
}
else
{
uint8_t v___x_439_; 
lean_inc_ref(v_msgData_295_);
v___x_439_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_295_);
v___y_426_ = v___x_439_;
goto v___jp_425_;
}
v___jp_301_:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Elab_Command_getScope___redArg(v___y_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v_currNamespace_312_; lean_object* v___x_313_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v_currNamespace_312_ = lean_ctor_get(v_a_311_, 2);
lean_inc(v_currNamespace_312_);
lean_dec(v_a_311_);
v___x_313_ = l_Lean_Elab_Command_getScope___redArg(v___y_309_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_349_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_349_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_349_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_349_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_openDecls_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_env_323_; lean_object* v_messages_324_; lean_object* v_scopes_325_; lean_object* v_usedQuotCtxts_326_; lean_object* v_nextMacroScope_327_; lean_object* v_maxRecDepth_328_; lean_object* v_ngen_329_; lean_object* v_auxDeclNGen_330_; lean_object* v_infoState_331_; lean_object* v_traceState_332_; lean_object* v_snapshotTasks_333_; lean_object* v_prevLinterStates_334_; lean_object* v_codeQualityEntryTasks_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_348_; 
v_openDecls_318_ = lean_ctor_get(v_a_314_, 3);
lean_inc(v_openDecls_318_);
lean_dec(v_a_314_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_currNamespace_312_);
lean_ctor_set(v___x_319_, 1, v_openDecls_318_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___y_303_);
lean_inc_ref(v___y_304_);
lean_inc_ref(v___y_302_);
v___x_321_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_321_, 0, v___y_302_);
lean_ctor_set(v___x_321_, 1, v___y_306_);
lean_ctor_set(v___x_321_, 2, v___y_305_);
lean_ctor_set(v___x_321_, 3, v___y_304_);
lean_ctor_set(v___x_321_, 4, v___x_320_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5, v___y_307_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5 + 1, v___y_308_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*5 + 2, v_isSilent_297_);
v___x_322_ = lean_st_ref_take(v___y_309_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
v_messages_324_ = lean_ctor_get(v___x_322_, 1);
v_scopes_325_ = lean_ctor_get(v___x_322_, 2);
v_usedQuotCtxts_326_ = lean_ctor_get(v___x_322_, 3);
v_nextMacroScope_327_ = lean_ctor_get(v___x_322_, 4);
v_maxRecDepth_328_ = lean_ctor_get(v___x_322_, 5);
v_ngen_329_ = lean_ctor_get(v___x_322_, 6);
v_auxDeclNGen_330_ = lean_ctor_get(v___x_322_, 7);
v_infoState_331_ = lean_ctor_get(v___x_322_, 8);
v_traceState_332_ = lean_ctor_get(v___x_322_, 9);
v_snapshotTasks_333_ = lean_ctor_get(v___x_322_, 10);
v_prevLinterStates_334_ = lean_ctor_get(v___x_322_, 11);
v_codeQualityEntryTasks_335_ = lean_ctor_get(v___x_322_, 12);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_348_ == 0)
{
v___x_337_ = v___x_322_;
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_codeQualityEntryTasks_335_);
lean_inc(v_prevLinterStates_334_);
lean_inc(v_snapshotTasks_333_);
lean_inc(v_traceState_332_);
lean_inc(v_infoState_331_);
lean_inc(v_auxDeclNGen_330_);
lean_inc(v_ngen_329_);
lean_inc(v_maxRecDepth_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_usedQuotCtxts_326_);
lean_inc(v_scopes_325_);
lean_inc(v_messages_324_);
lean_inc(v_env_323_);
lean_dec(v___x_322_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_box(0);
v___x_340_ = l_Lean_MessageLog_add(v___x_321_, v_messages_324_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___x_340_);
v___x_342_ = v___x_337_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_env_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_scopes_325_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_usedQuotCtxts_326_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 5, v_maxRecDepth_328_);
lean_ctor_set(v_reuseFailAlloc_347_, 6, v_ngen_329_);
lean_ctor_set(v_reuseFailAlloc_347_, 7, v_auxDeclNGen_330_);
lean_ctor_set(v_reuseFailAlloc_347_, 8, v_infoState_331_);
lean_ctor_set(v_reuseFailAlloc_347_, 9, v_traceState_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 10, v_snapshotTasks_333_);
lean_ctor_set(v_reuseFailAlloc_347_, 11, v_prevLinterStates_334_);
lean_ctor_set(v_reuseFailAlloc_347_, 12, v_codeQualityEntryTasks_335_);
v___x_342_ = v_reuseFailAlloc_347_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_st_ref_put(v___y_309_, v___x_342_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_339_);
v___x_345_ = v___x_316_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_339_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_currNamespace_312_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_303_);
v_a_350_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_313_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_313_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_303_);
v_a_358_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_310_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_310_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
v___jp_366_:
{
lean_object* v_fileName_372_; lean_object* v_fileMap_373_; uint8_t v_suppressElabErrors_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_393_; 
v_fileName_372_ = lean_ctor_get(v___y_298_, 0);
v_fileMap_373_ = lean_ctor_get(v___y_298_, 1);
v_suppressElabErrors_374_ = lean_ctor_get_uint8(v___y_298_, sizeof(void*)*10);
v___x_375_ = lean_box(v_suppressElabErrors_374_);
v___x_376_ = lean_box(v___y_367_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_377_, 0, v___x_375_);
lean_closure_set(v___f_377_, 1, v___x_376_);
v___x_378_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_295_);
v___x_379_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg(v___x_378_, v___y_299_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_393_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_393_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_393_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
lean_inc_ref_n(v_fileMap_373_, 2);
v___x_384_ = l_Lean_FileMap_toPosition(v_fileMap_373_, v___y_368_);
lean_dec(v___y_368_);
v___x_385_ = l_Lean_FileMap_toPosition(v_fileMap_373_, v___y_371_);
lean_dec(v___y_371_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___closed__0));
if (v_suppressElabErrors_374_ == 0)
{
lean_del_object(v___x_382_);
lean_dec_ref(v___f_377_);
v___y_302_ = v_fileName_372_;
v___y_303_ = v_a_380_;
v___y_304_ = v___x_387_;
v___y_305_ = v___x_386_;
v___y_306_ = v___x_384_;
v___y_307_ = v___y_369_;
v___y_308_ = v___y_370_;
v___y_309_ = v___y_299_;
goto v___jp_301_;
}
else
{
uint8_t v___x_388_; 
lean_inc(v_a_380_);
v___x_388_ = l_Lean_MessageData_hasTag(v___f_377_, v_a_380_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_391_; 
lean_dec_ref_known(v___x_386_, 1);
lean_dec_ref(v___x_384_);
lean_dec(v_a_380_);
v___x_389_ = lean_box(0);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_389_);
v___x_391_ = v___x_382_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_del_object(v___x_382_);
v___y_302_ = v_fileName_372_;
v___y_303_ = v_a_380_;
v___y_304_ = v___x_387_;
v___y_305_ = v___x_386_;
v___y_306_ = v___x_384_;
v___y_307_ = v___y_369_;
v___y_308_ = v___y_370_;
v___y_309_ = v___y_299_;
goto v___jp_301_;
}
}
}
}
v___jp_394_:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Syntax_getTailPos_x3f(v___y_396_, v___y_397_);
lean_dec(v___y_396_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_inc(v___y_399_);
v___y_367_ = v___y_395_;
v___y_368_ = v___y_399_;
v___y_369_ = v___y_397_;
v___y_370_ = v___y_398_;
v___y_371_ = v___y_399_;
goto v___jp_366_;
}
else
{
lean_object* v_val_401_; 
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_400_, 1);
v___y_367_ = v___y_395_;
v___y_368_ = v___y_399_;
v___y_369_ = v___y_397_;
v___y_370_ = v___y_398_;
v___y_371_ = v_val_401_;
goto v___jp_366_;
}
}
v___jp_402_:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Command_getRef___redArg(v___y_298_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v_ref_408_; lean_object* v___x_409_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v_ref_408_ = l_Lean_replaceRef(v_ref_294_, v_a_407_);
lean_dec(v_a_407_);
v___x_409_ = l_Lean_Syntax_getPos_x3f(v_ref_408_, v___y_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___y_395_ = v___y_403_;
v___y_396_ = v_ref_408_;
v___y_397_ = v___y_404_;
v___y_398_ = v___y_405_;
v___y_399_ = v___x_410_;
goto v___jp_394_;
}
else
{
lean_object* v_val_411_; 
v_val_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_409_, 1);
v___y_395_ = v___y_403_;
v___y_396_ = v_ref_408_;
v___y_397_ = v___y_404_;
v___y_398_ = v___y_405_;
v___y_399_ = v_val_411_;
goto v___jp_394_;
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_msgData_295_);
v_a_412_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_406_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_406_);
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
v___jp_421_:
{
if (v___y_424_ == 0)
{
v___y_403_ = v___y_422_;
v___y_404_ = v___y_423_;
v___y_405_ = v_severity_296_;
goto v___jp_402_;
}
else
{
v___y_403_ = v___y_422_;
v___y_404_ = v___y_423_;
v___y_405_ = v___x_420_;
goto v___jp_402_;
}
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_scopes_429_; lean_object* v___x_430_; lean_object* v_opts_431_; uint8_t v___x_432_; uint8_t v___x_433_; 
v___x_427_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_428_ = lean_st_ref_get(v___y_299_);
v_scopes_429_ = lean_ctor_get(v___x_428_, 2);
lean_inc(v_scopes_429_);
lean_dec(v___x_428_);
v___x_430_ = l_List_head_x21___redArg(v___x_427_, v_scopes_429_);
lean_dec(v_scopes_429_);
v_opts_431_ = lean_ctor_get(v___x_430_, 1);
lean_inc_ref(v_opts_431_);
lean_dec(v___x_430_);
v___x_432_ = 1;
v___x_433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_296_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_opts_431_);
v___y_422_ = v___y_426_;
v___y_423_ = v___y_426_;
v___y_424_ = v___x_433_;
goto v___jp_421_;
}
else
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = l_Lean_warningAsError;
v___x_435_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__8(v_opts_431_, v___x_434_);
lean_dec_ref(v_opts_431_);
v___y_422_ = v___y_426_;
v___y_423_ = v___y_426_;
v___y_424_ = v___x_435_;
goto v___jp_421_;
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_msgData_295_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4___boxed(lean_object* v_ref_440_, lean_object* v_msgData_441_, lean_object* v_severity_442_, lean_object* v_isSilent_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v_severity_boxed_447_; uint8_t v_isSilent_boxed_448_; lean_object* v_res_449_; 
v_severity_boxed_447_ = lean_unbox(v_severity_442_);
v_isSilent_boxed_448_ = lean_unbox(v_isSilent_443_);
v_res_449_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4(v_ref_440_, v_msgData_441_, v_severity_boxed_447_, v_isSilent_boxed_448_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v_ref_440_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2(lean_object* v_ref_450_, lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
uint8_t v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; 
v___x_455_ = 1;
v___x_456_ = 0;
v___x_457_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4(v_ref_450_, v_msgData_451_, v___x_455_, v___x_456_, v___y_452_, v___y_453_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2___boxed(lean_object* v_ref_458_, lean_object* v_msgData_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2(v_ref_458_, v_msgData_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_ref_458_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__0));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__2));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(lean_object* v_linterOption_470_, lean_object* v_stx_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_name_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_494_; 
v_name_476_ = lean_ctor_get(v_linterOption_470_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_linterOption_470_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v_linterOption_470_, 1);
lean_dec(v_unused_495_);
v___x_478_ = v_linterOption_470_;
v_isShared_479_ = v_isSharedCheck_494_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_name_476_);
lean_dec(v_linterOption_470_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_494_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__1);
lean_inc(v_name_476_);
v___x_481_ = l_Lean_MessageData_ofName(v_name_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 7);
lean_ctor_set(v___x_478_, 1, v___x_481_);
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_493_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_disable_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_484_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___closed__3);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v_disable_486_ = l_Lean_MessageData_note(v___x_485_);
v___x_487_ = l_Lean_Linter_linterMessageTag;
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v_msg_472_);
lean_ctor_set(v___x_488_, 1, v_disable_486_);
v___x_489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_490_, 0, v_name_476_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_inc(v_stx_471_);
v___x_491_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_491_, 0, v_stx_471_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2(v_stx_471_, v___x_491_, v___y_473_, v___y_474_);
lean_dec(v_stx_471_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___boxed(lean_object* v_linterOption_496_, lean_object* v_stx_497_, lean_object* v_msg_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(v_linterOption_496_, v_stx_497_, v_msg_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_502_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__0));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__2));
v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__4));
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_as_x27_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
if (lean_obj_tag(v_as_x27_514_) == 0)
{
lean_object* v___x_519_; 
lean_dec(v___x_513_);
lean_dec_ref(v___x_512_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_b_515_);
return v___x_519_;
}
else
{
lean_object* v_head_520_; lean_object* v_tail_521_; uint8_t v___x_522_; 
v_head_520_ = lean_ctor_get(v_as_x27_514_, 0);
v_tail_521_ = lean_ctor_get(v_as_x27_514_, 1);
v___x_522_ = l_Lean_NameSet_contains(v_b_515_, v_head_520_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = 1;
lean_inc_n(v_head_520_, 2);
v___x_524_ = l_Lean_NameSet_insert(v_b_515_, v_head_520_);
lean_inc_ref(v___x_512_);
v___x_525_ = l_Lean_Environment_contains(v___x_512_, v_head_520_, v___x_523_);
if (v___x_525_ == 0)
{
v_as_x27_514_ = v_tail_521_;
v_b_515_ = v___x_524_;
goto _start;
}
else
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Linter_InternalModule_isInternalDecl(v_head_520_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_529_ = l_Lean_Elab_Command_getRef___redArg(v___y_516_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__1);
lean_inc(v_head_520_);
v___x_532_ = l_Lean_MessageData_ofConstName(v_head_520_, v___x_527_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__3);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc(v___x_513_);
v___x_536_ = l_Lean_MessageData_ofName(v___x_513_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___closed__5);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(v___x_528_, v_a_530_, v___x_539_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_dec_ref_known(v___x_540_, 1);
v_as_x27_514_ = v_tail_521_;
v_b_515_ = v___x_524_;
goto _start;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v___x_524_);
lean_dec(v___x_513_);
lean_dec_ref(v___x_512_);
v_a_542_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v___x_524_);
lean_dec(v___x_513_);
lean_dec_ref(v___x_512_);
v_a_550_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_529_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_529_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
v_as_x27_514_ = v_tail_521_;
v_b_515_ = v___x_524_;
goto _start;
}
}
}
else
{
v_as_x27_514_ = v_tail_521_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg___boxed(lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_as_x27_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_560_, v___x_561_, v_as_x27_562_, v_b_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_as_x27_562_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_as_570_, size_t v_sz_571_, size_t v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_572_, v_sz_571_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_569_);
lean_dec_ref(v___x_568_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_b_573_);
return v___x_578_;
}
else
{
lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
v_snd_579_ = lean_ctor_get(v_b_573_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v_b_573_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_b_573_, 0);
lean_dec(v_unused_603_);
v___x_581_ = v_b_573_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_dec(v_b_573_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_box(0);
v_a_584_ = lean_array_uget_borrowed(v_as_570_, v_i_572_);
lean_inc(v_a_584_);
v___x_585_ = l_Lean_Linter_getNewDecls(v_a_584_);
lean_inc(v___x_569_);
lean_inc_ref(v___x_568_);
v___x_586_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_568_, v___x_569_, v___x_585_, v_snd_579_, v___y_574_, v___y_575_);
lean_dec(v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_a_587_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_589_ = v___x_581_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_a_587_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
size_t v___x_590_; size_t v___x_591_; 
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_i_572_, v___x_590_);
v_i_572_ = v___x_591_;
v_b_573_ = v___x_589_;
goto _start;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_del_object(v___x_581_);
lean_dec(v___x_569_);
lean_dec_ref(v___x_568_);
v_a_594_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_586_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_586_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v_as_606_, lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_614_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_604_, v___x_605_, v_as_606_, v_sz_boxed_613_, v_i_boxed_614_, v_b_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec_ref(v_as_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object* v___x_616_, lean_object* v___x_617_, lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v___x_617_);
lean_dec_ref(v___x_616_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_b_621_);
return v___x_626_;
}
else
{
lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_650_; 
v_snd_627_ = lean_ctor_get(v_b_621_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_b_621_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_b_621_, 0);
lean_dec(v_unused_651_);
v___x_629_ = v_b_621_;
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_dec(v_b_621_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_650_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_box(0);
v_a_632_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
lean_inc(v_a_632_);
v___x_633_ = l_Lean_Linter_getNewDecls(v_a_632_);
lean_inc(v___x_617_);
lean_inc_ref(v___x_616_);
v___x_634_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_616_, v___x_617_, v___x_633_, v_snd_627_, v___y_622_, v___y_623_);
lean_dec(v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_a_635_);
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_a_635_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_620_, v___x_638_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_616_, v___x_617_, v_as_618_, v_sz_619_, v___x_639_, v___x_637_, v___y_622_, v___y_623_);
return v___x_640_;
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_629_);
lean_dec(v___x_617_);
lean_dec_ref(v___x_616_);
v_a_642_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_634_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_634_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_as_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; lean_object* v_res_663_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_662_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_652_, v___x_653_, v_as_654_, v_sz_boxed_661_, v_i_boxed_662_, v_b_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_as_654_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v_as_666_, size_t v_sz_667_, size_t v_i_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_668_, v_sz_667_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_b_669_);
return v___x_674_;
}
else
{
lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_698_; 
v_snd_675_ = lean_ctor_get(v_b_669_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_b_669_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_b_669_, 0);
lean_dec(v_unused_699_);
v___x_677_ = v_b_669_;
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_dec(v_b_669_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(0);
v_a_680_ = lean_array_uget_borrowed(v_as_666_, v_i_668_);
lean_inc(v_a_680_);
v___x_681_ = l_Lean_Linter_getNewDecls(v_a_680_);
lean_inc(v___x_665_);
lean_inc_ref(v___x_664_);
v___x_682_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_664_, v___x_665_, v___x_681_, v_snd_675_, v___y_670_, v___y_671_);
lean_dec(v___x_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_a_683_);
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_a_683_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_668_, v___x_686_);
v_i_668_ = v___x_687_;
v_b_669_ = v___x_685_;
goto _start;
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_del_object(v___x_677_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
v_a_690_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_682_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_682_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_710_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_700_, v___x_701_, v_as_702_, v_sz_boxed_709_, v_i_boxed_710_, v_b_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_as_702_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v_as_714_, size_t v_sz_715_, size_t v_i_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v___x_713_);
lean_dec_ref(v___x_712_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_717_);
return v___x_722_;
}
else
{
lean_object* v_snd_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_746_; 
v_snd_723_ = lean_ctor_get(v_b_717_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_b_717_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_b_717_, 0);
lean_dec(v_unused_747_);
v___x_725_ = v_b_717_;
v_isShared_726_ = v_isSharedCheck_746_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_snd_723_);
lean_dec(v_b_717_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_746_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_box(0);
v_a_728_ = lean_array_uget_borrowed(v_as_714_, v_i_716_);
lean_inc(v_a_728_);
v___x_729_ = l_Lean_Linter_getNewDecls(v_a_728_);
lean_inc(v___x_713_);
lean_inc_ref(v___x_712_);
v___x_730_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_712_, v___x_713_, v___x_729_, v_snd_723_, v___y_718_, v___y_719_);
lean_dec(v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_a_731_);
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_733_ = v___x_725_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_731_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_716_, v___x_734_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_712_, v___x_713_, v_as_714_, v_sz_715_, v___x_735_, v___x_733_, v___y_718_, v___y_719_);
return v___x_736_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_del_object(v___x_725_);
lean_dec(v___x_713_);
lean_dec_ref(v___x_712_);
v_a_738_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_730_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_730_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_as_750_, lean_object* v_sz_751_, lean_object* v_i_752_, lean_object* v_b_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_751_);
lean_dec(v_sz_751_);
v_i_boxed_758_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_748_, v___x_749_, v_as_750_, v_sz_boxed_757_, v_i_boxed_758_, v_b_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v_as_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object* v_init_760_, lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_n_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
if (lean_obj_tag(v_n_763_) == 0)
{
lean_object* v_cs_768_; lean_object* v___x_769_; lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; 
v_cs_768_ = lean_ctor_get(v_n_763_, 0);
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_b_764_);
v_sz_771_ = lean_array_size(v_cs_768_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_760_, v___x_761_, v___x_762_, v_cs_768_, v_sz_771_, v___x_772_, v___x_770_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_788_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_788_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fst_778_; 
v_fst_778_ = lean_ctor_get(v_a_774_, 0);
if (lean_obj_tag(v_fst_778_) == 0)
{
lean_object* v_snd_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v_snd_779_ = lean_ctor_get(v_a_774_, 1);
lean_inc(v_snd_779_);
lean_dec(v_a_774_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_snd_779_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; 
lean_inc_ref(v_fst_778_);
lean_dec(v_a_774_);
v_val_784_ = lean_ctor_get(v_fst_778_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_fst_778_, 1);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_val_784_);
v___x_786_ = v___x_776_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_val_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_773_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_773_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_vs_797_; lean_object* v___x_798_; lean_object* v___x_799_; size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_vs_797_ = lean_ctor_get(v_n_763_, 0);
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v_b_764_);
v_sz_800_ = lean_array_size(v_vs_797_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_761_, v___x_762_, v_vs_797_, v_sz_800_, v___x_801_, v___x_799_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_817_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_817_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_817_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_fst_807_; 
v_fst_807_ = lean_ctor_get(v_a_803_, 0);
if (lean_obj_tag(v_fst_807_) == 0)
{
lean_object* v_snd_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_snd_808_ = lean_ctor_get(v_a_803_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_803_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_snd_808_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v_val_813_; lean_object* v___x_815_; 
lean_inc_ref(v_fst_807_);
lean_dec(v_a_803_);
v_val_813_ = lean_ctor_get(v_fst_807_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_fst_807_, 1);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_val_813_);
v___x_815_ = v___x_805_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_val_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_802_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_802_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object* v_init_826_, lean_object* v___x_827_, lean_object* v___x_828_, lean_object* v_as_829_, size_t v_sz_830_, size_t v_i_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = lean_usize_dec_lt(v_i_831_, v_sz_830_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_dec(v___x_828_);
lean_dec_ref(v___x_827_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_b_832_);
return v___x_837_;
}
else
{
lean_object* v_snd_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_872_; 
v_snd_838_ = lean_ctor_get(v_b_832_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_b_832_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_b_832_, 0);
lean_dec(v_unused_873_);
v___x_840_ = v_b_832_;
v_isShared_841_ = v_isSharedCheck_872_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_838_);
lean_dec(v_b_832_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_872_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_844_; 
v___x_842_ = lean_box(0);
v_a_843_ = lean_array_uget_borrowed(v_as_829_, v_i_831_);
lean_inc(v_snd_838_);
lean_inc(v___x_828_);
lean_inc_ref(v___x_827_);
v___x_844_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_826_, v___x_827_, v___x_828_, v_a_843_, v_snd_838_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_863_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_863_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
if (lean_obj_tag(v_a_845_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec(v___x_828_);
lean_dec_ref(v___x_827_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_a_845_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_849_);
v___x_851_ = v___x_840_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_snd_838_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_838_);
v_a_856_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v_a_845_, 1);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_a_856_);
lean_ctor_set(v___x_840_, 0, v___x_842_);
v___x_858_ = v___x_840_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_a_856_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
size_t v___x_859_; size_t v___x_860_; 
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_add(v_i_831_, v___x_859_);
v_i_831_ = v___x_860_;
v_b_832_ = v___x_858_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_840_);
lean_dec(v_snd_838_);
lean_dec(v___x_828_);
lean_dec_ref(v___x_827_);
v_a_864_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_844_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_844_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_sz_boxed_884_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_885_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_874_, v___x_875_, v___x_876_, v_as_877_, v_sz_boxed_884_, v_i_boxed_885_, v_b_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_as_877_);
lean_dec(v_init_874_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object* v_init_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_n_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_887_, v___x_888_, v___x_889_, v_n_890_, v_b_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_n_890_);
lean_dec(v_init_887_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_t_898_, lean_object* v_init_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_root_903_; lean_object* v_tail_904_; lean_object* v___x_905_; 
v_root_903_ = lean_ctor_get(v_t_898_, 0);
v_tail_904_ = lean_ctor_get(v_t_898_, 1);
lean_inc(v___x_897_);
lean_inc_ref(v___x_896_);
lean_inc(v_init_899_);
v___x_905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_899_, v___x_896_, v___x_897_, v_root_903_, v_init_899_, v___y_900_, v___y_901_);
lean_dec(v_init_899_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_942_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_942_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
if (lean_obj_tag(v_a_906_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; 
lean_dec(v___x_897_);
lean_dec_ref(v___x_896_);
v_a_910_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v_a_906_, 1);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v_a_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; size_t v_sz_917_; size_t v___x_918_; lean_object* v___x_919_; 
lean_del_object(v___x_908_);
v_a_914_ = lean_ctor_get(v_a_906_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v_a_906_, 1);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_a_914_);
v_sz_917_ = lean_array_size(v_tail_904_);
v___x_918_ = ((size_t)0ULL);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_896_, v___x_897_, v_tail_904_, v_sz_917_, v___x_918_, v___x_916_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_fst_924_; 
v_fst_924_ = lean_ctor_get(v_a_920_, 0);
if (lean_obj_tag(v_fst_924_) == 0)
{
lean_object* v_snd_925_; lean_object* v___x_927_; 
v_snd_925_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_925_);
lean_dec(v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_snd_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_snd_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
else
{
lean_object* v_val_929_; lean_object* v___x_931_; 
lean_inc_ref(v_fst_924_);
lean_dec(v_a_920_);
v_val_929_ = lean_ctor_get(v_fst_924_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v_fst_924_, 1);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_val_929_);
v___x_931_ = v___x_922_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_val_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_919_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_919_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v___x_897_);
lean_dec_ref(v___x_896_);
v_a_943_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_905_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_905_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object* v___x_951_, lean_object* v___x_952_, lean_object* v_t_953_, lean_object* v_init_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v___x_951_, v___x_952_, v_t_953_, v_init_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_t_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object* v_o_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_env_964_; lean_object* v___x_965_; lean_object* v_toEnvExtension_966_; lean_object* v_asyncMode_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v_merged_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v___x_962_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_963_ = lean_st_ref_get(v___y_960_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_966_ = lean_ctor_get(v___x_965_, 0);
v_asyncMode_967_ = lean_ctor_get(v_toEnvExtension_966_, 2);
v___x_968_ = lean_box(0);
v___x_969_ = 0;
v___x_970_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_962_, v___x_965_, v_env_964_, v_asyncMode_967_, v___x_968_, v___x_969_);
v_merged_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v___x_970_, 1);
lean_dec(v_unused_980_);
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_merged_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v_merged_971_);
lean_ctor_set(v___x_973_, 0, v_o_959_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_o_959_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_merged_971_);
v___x_976_ = v_reuseFailAlloc_978_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_981_, v___y_982_);
lean_dec(v___y_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_scopes_990_; lean_object* v___x_991_; lean_object* v_opts_992_; lean_object* v___x_993_; 
v___x_988_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_989_ = lean_st_ref_get(v___y_986_);
v_scopes_990_ = lean_ctor_get(v___x_989_, 2);
lean_inc(v_scopes_990_);
lean_dec(v___x_989_);
v___x_991_ = l_List_head_x21___redArg(v___x_988_, v_scopes_990_);
lean_dec(v_scopes_990_);
v_opts_992_ = lean_ctor_get(v___x_991_, 1);
lean_inc_ref(v_opts_992_);
lean_dec(v___x_991_);
v___x_993_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_opts_992_, v___y_986_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_messages_1003_; uint8_t v___x_1004_; 
v___x_1002_ = lean_st_ref_get(v___y_1000_);
v_messages_1003_ = lean_ctor_get(v___x_1002_, 1);
lean_inc_ref(v_messages_1003_);
lean_dec(v___x_1002_);
v___x_1004_ = l_Lean_MessageLog_hasErrors(v_messages_1003_);
lean_dec_ref(v_messages_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1045_; 
v___x_1005_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_999_, v___y_1000_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_1011_ = l_Lean_Linter_getLinterValue(v___x_1010_, v_a_1006_);
lean_dec(v_a_1006_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1012_);
v___x_1014_ = v___x_1008_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1016_; lean_object* v_env_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1016_ = lean_st_ref_get(v___y_1000_);
v_env_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_ref(v_env_1017_);
lean_dec(v___x_1016_);
v___x_1018_ = l_Lean_Environment_mainModule(v_env_1017_);
v___x_1019_ = l_Lean_Linter_InternalModule_isInternalModule(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_env_1017_);
v___x_1020_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1020_);
v___x_1022_ = v___x_1008_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1027_; 
lean_del_object(v___x_1008_);
v___x_1024_ = l_Lean_NameSet_empty;
v___x_1025_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___y_1000_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v_env_1017_, v___x_1018_, v_a_1026_, v___x_1024_, v___y_999_, v___y_1000_);
lean_dec(v_a_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1036_);
v___x_1029_ = v___x_1027_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1027_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(0);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1027_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1027_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(v_x_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v_x_1048_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object* v_o_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1067_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object* v_o_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(v_o_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_as_1079_, lean_object* v_as_x27_1080_, lean_object* v_b_1081_, lean_object* v_a_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___redArg(v___x_1077_, v___x_1078_, v_as_x27_1080_, v_b_1081_, v___y_1083_, v___y_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v_as_1089_, lean_object* v_as_x27_1090_, lean_object* v_b_1091_, lean_object* v_a_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v___x_1087_, v___x_1088_, v_as_1089_, v_as_x27_1090_, v_b_1091_, v_a_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v_as_x27_1090_);
lean_dec(v_as_1089_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7(lean_object* v_msgData_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___redArg(v_msgData_1097_, v___y_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_msgData_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1_spec__2_spec__4_spec__7(v_msgData_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModuleLinter));
v___x_1109_ = l_Lean_Elab_Command_addLinter(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
return v_res_1111_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_InternalModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_InternalModule_0__Lean_Linter_initFn_00___x40_Lean_Linter_InternalModule_2831130310____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_coreInternal_internalModule = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_coreInternal_internalModule);
lean_dec_ref(res);
res = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_InternalModule(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* initialize_Lean_PrivateName(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_InternalModule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_InternalModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_InternalModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_InternalModule(builtin);
}
#ifdef __cplusplus
}
#endif
