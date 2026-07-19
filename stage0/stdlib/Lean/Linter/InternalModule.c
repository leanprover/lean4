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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "` is a non-internal declaration in the internal module `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 445, .m_capacity = 445, .m_length = 444, .m_data = "`; declarations in internal modules should themselves be internal.\n\nMake the declaration private, or put it into an internal namespace, or, if the declaration is supposed to be part of the standard library, move it into a file that is part of the standard library.\n\nFor core-specific helper functions about basic types, recall that after `open Lean`, a declaration like `Lean.List.foo` will be available for generalized field notation on lists."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___closed__0 = (const lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_InternalModule_internalModuleLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_InternalModule_internalModuleLinter___closed__0_value)} };
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
return v___x_168_;
}
else
{
if (v___x_170_ == 0)
{
return v___x_168_;
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
v___y_193_ = v___x_195_;
goto v___jp_192_;
}
else
{
if (v___x_197_ == 0)
{
v___y_193_ = v___x_195_;
goto v___jp_192_;
}
else
{
size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = ((size_t)0ULL);
v___x_199_ = lean_usize_once(&l_Lean_Linter_InternalModule_isInternalDecl___closed__2, &l_Lean_Linter_InternalModule_isInternalDecl___closed__2_once, _init_l_Lean_Linter_InternalModule_isInternalDecl___closed__2);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_InternalModule_isInternalModule_spec__0(v_declName_191_, v___x_196_, v___x_198_, v___x_199_);
v___y_193_ = v___x_200_;
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
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_isInternalDecl___boxed(lean_object* v_declName_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_Linter_InternalModule_isInternalDecl(v_declName_201_);
lean_dec(v_declName_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v_infoState_207_; lean_object* v_trees_208_; lean_object* v___x_209_; 
v___x_206_ = lean_st_ref_get(v___y_204_);
v_infoState_207_ = lean_ctor_get(v___x_206_, 8);
lean_inc_ref(v_infoState_207_);
lean_dec(v___x_206_);
v_trees_208_ = lean_ctor_get(v_infoState_207_, 2);
lean_inc_ref(v_trees_208_);
lean_dec_ref(v_infoState_207_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_trees_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg___boxed(lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_210_);
lean_dec(v___y_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___boxed(lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(lean_object* v_opts_221_, lean_object* v_opt_222_){
_start:
{
lean_object* v_name_223_; lean_object* v_defValue_224_; lean_object* v_map_225_; lean_object* v___x_226_; 
v_name_223_ = lean_ctor_get(v_opt_222_, 0);
v_defValue_224_ = lean_ctor_get(v_opt_222_, 1);
v_map_225_ = lean_ctor_get(v_opts_221_, 0);
v___x_226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_225_, v_name_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = lean_unbox(v_defValue_224_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
if (lean_obj_tag(v_val_228_) == 1)
{
uint8_t v_v_229_; 
v_v_229_ = lean_ctor_get_uint8(v_val_228_, 0);
lean_dec_ref_known(v_val_228_, 0);
return v_v_229_;
}
else
{
uint8_t v___x_230_; 
lean_dec(v_val_228_);
v___x_230_ = lean_unbox(v_defValue_224_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8___boxed(lean_object* v_opts_231_, lean_object* v_opt_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_231_, v_opt_232_);
lean_dec_ref(v_opt_232_);
lean_dec_ref(v_opts_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(uint8_t v___y_236_, uint8_t v_suppressElabErrors_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 1)
{
lean_object* v_pre_239_; 
v_pre_239_ = lean_ctor_get(v_x_238_, 0);
if (lean_obj_tag(v_pre_239_) == 0)
{
lean_object* v_str_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_str_240_ = lean_ctor_get(v_x_238_, 1);
v___x_241_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___closed__0));
v___x_242_ = lean_string_dec_eq(v_str_240_, v___x_241_);
if (v___x_242_ == 0)
{
return v___y_236_;
}
else
{
return v_suppressElabErrors_237_;
}
}
else
{
return v___y_236_;
}
}
else
{
return v___y_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed(lean_object* v___y_243_, lean_object* v_suppressElabErrors_244_, lean_object* v_x_245_){
_start:
{
uint8_t v___y_9118__boxed_246_; uint8_t v_suppressElabErrors_boxed_247_; uint8_t v_res_248_; lean_object* v_r_249_; 
v___y_9118__boxed_246_ = lean_unbox(v___y_243_);
v_suppressElabErrors_boxed_247_ = lean_unbox(v_suppressElabErrors_244_);
v_res_248_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(v___y_9118__boxed_246_, v_suppressElabErrors_boxed_247_, v_x_245_);
lean_dec(v_x_245_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_250_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_254_);
lean_ctor_set(v___x_255_, 4, v___x_253_);
lean_ctor_set(v___x_255_, 5, v___x_253_);
lean_ctor_set(v___x_255_, 6, v___x_253_);
lean_ctor_set(v___x_255_, 7, v___x_253_);
lean_ctor_set(v___x_255_, 8, v___x_253_);
lean_ctor_set(v___x_255_, 9, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(32u);
v___x_257_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((size_t)5ULL);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_unsigned_to_nat(32u);
v___x_262_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3);
v___x_264_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_260_);
lean_ctor_set(v___x_264_, 3, v___x_260_);
lean_ctor_set_usize(v___x_264_, 4, v___x_259_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_box(1);
v___x_266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4);
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_msgData_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_env_273_; lean_object* v___x_274_; lean_object* v_scopes_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_opts_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_272_ = lean_st_ref_get(v___y_270_);
v_env_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_env_273_);
lean_dec(v___x_272_);
v___x_274_ = lean_st_ref_get(v___y_270_);
v_scopes_275_ = lean_ctor_get(v___x_274_, 2);
lean_inc(v_scopes_275_);
lean_dec(v___x_274_);
v___x_276_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_277_ = l_List_head_x21___redArg(v___x_276_, v_scopes_275_);
lean_dec(v_scopes_275_);
v_opts_278_ = lean_ctor_get(v___x_277_, 1);
lean_inc_ref(v_opts_278_);
lean_dec(v___x_277_);
v___x_279_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2);
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5);
v___x_281_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_281_, 0, v_env_273_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_280_);
lean_ctor_set(v___x_281_, 3, v_opts_278_);
v___x_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_msgData_269_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_284_, v___y_285_);
lean_dec(v___y_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(lean_object* v_ref_289_, lean_object* v_msgData_290_, uint8_t v_severity_291_, uint8_t v_isSilent_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; uint8_t v___y_303_; lean_object* v___y_304_; uint8_t v___y_360_; lean_object* v___y_361_; uint8_t v___y_362_; uint8_t v___y_363_; lean_object* v___y_364_; uint8_t v___y_388_; uint8_t v___y_389_; lean_object* v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; uint8_t v___y_396_; uint8_t v___y_397_; uint8_t v___y_398_; uint8_t v___x_413_; uint8_t v___y_415_; uint8_t v___y_416_; uint8_t v___y_417_; uint8_t v___y_419_; uint8_t v___x_431_; 
v___x_413_ = 2;
v___x_431_ = l_Lean_instBEqMessageSeverity_beq(v_severity_291_, v___x_413_);
if (v___x_431_ == 0)
{
v___y_419_ = v___x_431_;
goto v___jp_418_;
}
else
{
uint8_t v___x_432_; 
lean_inc_ref(v_msgData_290_);
v___x_432_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_290_);
v___y_419_ = v___x_432_;
goto v___jp_418_;
}
v___jp_296_:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Elab_Command_getScope___redArg(v___y_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = l_Lean_Elab_Command_getScope___redArg(v___y_304_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_342_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_342_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_342_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_342_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_currNamespace_313_; lean_object* v_openDecls_314_; lean_object* v_env_315_; lean_object* v_messages_316_; lean_object* v_scopes_317_; lean_object* v_usedQuotCtxts_318_; lean_object* v_nextMacroScope_319_; lean_object* v_maxRecDepth_320_; lean_object* v_ngen_321_; lean_object* v_auxDeclNGen_322_; lean_object* v_infoState_323_; lean_object* v_traceState_324_; lean_object* v_snapshotTasks_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_341_; 
v___x_312_ = lean_st_ref_take(v___y_304_);
v_currNamespace_313_ = lean_ctor_get(v_a_306_, 2);
lean_inc(v_currNamespace_313_);
lean_dec(v_a_306_);
v_openDecls_314_ = lean_ctor_get(v_a_308_, 3);
lean_inc(v_openDecls_314_);
lean_dec(v_a_308_);
v_env_315_ = lean_ctor_get(v___x_312_, 0);
v_messages_316_ = lean_ctor_get(v___x_312_, 1);
v_scopes_317_ = lean_ctor_get(v___x_312_, 2);
v_usedQuotCtxts_318_ = lean_ctor_get(v___x_312_, 3);
v_nextMacroScope_319_ = lean_ctor_get(v___x_312_, 4);
v_maxRecDepth_320_ = lean_ctor_get(v___x_312_, 5);
v_ngen_321_ = lean_ctor_get(v___x_312_, 6);
v_auxDeclNGen_322_ = lean_ctor_get(v___x_312_, 7);
v_infoState_323_ = lean_ctor_get(v___x_312_, 8);
v_traceState_324_ = lean_ctor_get(v___x_312_, 9);
v_snapshotTasks_325_ = lean_ctor_get(v___x_312_, 10);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_341_ == 0)
{
v___x_327_ = v___x_312_;
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snapshotTasks_325_);
lean_inc(v_traceState_324_);
lean_inc(v_infoState_323_);
lean_inc(v_auxDeclNGen_322_);
lean_inc(v_ngen_321_);
lean_inc(v_maxRecDepth_320_);
lean_inc(v_nextMacroScope_319_);
lean_inc(v_usedQuotCtxts_318_);
lean_inc(v_scopes_317_);
lean_inc(v_messages_316_);
lean_inc(v_env_315_);
lean_dec(v___x_312_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_currNamespace_313_);
lean_ctor_set(v___x_329_, 1, v_openDecls_314_);
v___x_330_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___y_298_);
lean_inc_ref(v___y_299_);
lean_inc_ref(v___y_297_);
v___x_331_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_331_, 0, v___y_297_);
lean_ctor_set(v___x_331_, 1, v___y_300_);
lean_ctor_set(v___x_331_, 2, v___y_302_);
lean_ctor_set(v___x_331_, 3, v___y_299_);
lean_ctor_set(v___x_331_, 4, v___x_330_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5, v___y_303_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5 + 1, v___y_301_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*5 + 2, v_isSilent_292_);
v___x_332_ = l_Lean_MessageLog_add(v___x_331_, v_messages_316_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_332_);
v___x_334_ = v___x_327_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_env_315_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_scopes_317_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_usedQuotCtxts_318_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_nextMacroScope_319_);
lean_ctor_set(v_reuseFailAlloc_340_, 5, v_maxRecDepth_320_);
lean_ctor_set(v_reuseFailAlloc_340_, 6, v_ngen_321_);
lean_ctor_set(v_reuseFailAlloc_340_, 7, v_auxDeclNGen_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 8, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_340_, 9, v_traceState_324_);
lean_ctor_set(v_reuseFailAlloc_340_, 10, v_snapshotTasks_325_);
v___x_334_ = v_reuseFailAlloc_340_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = lean_st_ref_set(v___y_304_, v___x_334_);
v___x_336_ = lean_box(0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_336_);
v___x_338_ = v___x_310_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_306_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v___y_298_);
v_a_343_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_307_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_307_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v___y_302_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v___y_298_);
v_a_351_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_305_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_305_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
v___jp_359_:
{
lean_object* v_fileName_365_; lean_object* v_fileMap_366_; uint8_t v_suppressElabErrors_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_386_; 
v_fileName_365_ = lean_ctor_get(v___y_293_, 0);
v_fileMap_366_ = lean_ctor_get(v___y_293_, 1);
v_suppressElabErrors_367_ = lean_ctor_get_uint8(v___y_293_, sizeof(void*)*10);
v___x_368_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_290_);
v___x_369_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v___x_368_, v___y_294_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_inc_ref_n(v_fileMap_366_, 2);
v___x_374_ = l_Lean_FileMap_toPosition(v_fileMap_366_, v___y_361_);
lean_dec(v___y_361_);
v___x_375_ = l_Lean_FileMap_toPosition(v_fileMap_366_, v___y_364_);
lean_dec(v___y_364_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___x_377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0));
if (v_suppressElabErrors_367_ == 0)
{
lean_del_object(v___x_372_);
v___y_297_ = v_fileName_365_;
v___y_298_ = v_a_370_;
v___y_299_ = v___x_377_;
v___y_300_ = v___x_374_;
v___y_301_ = v___y_362_;
v___y_302_ = v___x_376_;
v___y_303_ = v___y_363_;
v___y_304_ = v___y_294_;
goto v___jp_296_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___f_380_; uint8_t v___x_381_; 
v___x_378_ = lean_box(v___y_360_);
v___x_379_ = lean_box(v_suppressElabErrors_367_);
v___f_380_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_380_, 0, v___x_378_);
lean_closure_set(v___f_380_, 1, v___x_379_);
lean_inc(v_a_370_);
v___x_381_ = l_Lean_MessageData_hasTag(v___f_380_, v_a_370_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec_ref_known(v___x_376_, 1);
lean_dec_ref(v___x_374_);
lean_dec(v_a_370_);
v___x_382_ = lean_box(0);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_382_);
v___x_384_ = v___x_372_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_del_object(v___x_372_);
v___y_297_ = v_fileName_365_;
v___y_298_ = v_a_370_;
v___y_299_ = v___x_377_;
v___y_300_ = v___x_374_;
v___y_301_ = v___y_362_;
v___y_302_ = v___x_376_;
v___y_303_ = v___y_363_;
v___y_304_ = v___y_294_;
goto v___jp_296_;
}
}
}
}
v___jp_387_:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Syntax_getTailPos_x3f(v___y_390_, v___y_391_);
lean_dec(v___y_390_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_inc(v___y_392_);
v___y_360_ = v___y_388_;
v___y_361_ = v___y_392_;
v___y_362_ = v___y_389_;
v___y_363_ = v___y_391_;
v___y_364_ = v___y_392_;
goto v___jp_359_;
}
else
{
lean_object* v_val_394_; 
v_val_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_393_, 1);
v___y_360_ = v___y_388_;
v___y_361_ = v___y_392_;
v___y_362_ = v___y_389_;
v___y_363_ = v___y_391_;
v___y_364_ = v_val_394_;
goto v___jp_359_;
}
}
v___jp_395_:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_Command_getRef___redArg(v___y_293_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_ref_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_ref_401_ = l_Lean_replaceRef(v_ref_289_, v_a_400_);
lean_dec(v_a_400_);
v___x_402_ = l_Lean_Syntax_getPos_x3f(v_ref_401_, v___y_397_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___y_388_ = v___y_396_;
v___y_389_ = v___y_398_;
v___y_390_ = v_ref_401_;
v___y_391_ = v___y_397_;
v___y_392_ = v___x_403_;
goto v___jp_387_;
}
else
{
lean_object* v_val_404_; 
v_val_404_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v___x_402_, 1);
v___y_388_ = v___y_396_;
v___y_389_ = v___y_398_;
v___y_390_ = v_ref_401_;
v___y_391_ = v___y_397_;
v___y_392_ = v_val_404_;
goto v___jp_387_;
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_msgData_290_);
v_a_405_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_399_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
v___jp_414_:
{
if (v___y_417_ == 0)
{
v___y_396_ = v___y_415_;
v___y_397_ = v___y_416_;
v___y_398_ = v_severity_291_;
goto v___jp_395_;
}
else
{
v___y_396_ = v___y_415_;
v___y_397_ = v___y_416_;
v___y_398_ = v___x_413_;
goto v___jp_395_;
}
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; lean_object* v_scopes_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_opts_424_; uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_420_ = lean_st_ref_get(v___y_294_);
v_scopes_421_ = lean_ctor_get(v___x_420_, 2);
lean_inc(v_scopes_421_);
lean_dec(v___x_420_);
v___x_422_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_423_ = l_List_head_x21___redArg(v___x_422_, v_scopes_421_);
lean_dec(v_scopes_421_);
v_opts_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc_ref(v_opts_424_);
lean_dec(v___x_423_);
v___x_425_ = 1;
v___x_426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_291_, v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v_opts_424_);
v___y_415_ = v___y_419_;
v___y_416_ = v___y_419_;
v___y_417_ = v___x_426_;
goto v___jp_414_;
}
else
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_warningAsError;
v___x_428_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_424_, v___x_427_);
lean_dec_ref(v_opts_424_);
v___y_415_ = v___y_419_;
v___y_416_ = v___y_419_;
v___y_417_ = v___x_428_;
goto v___jp_414_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v_msgData_290_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_433_, lean_object* v_msgData_434_, lean_object* v_severity_435_, lean_object* v_isSilent_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v_severity_boxed_440_; uint8_t v_isSilent_boxed_441_; lean_object* v_res_442_; 
v_severity_boxed_440_ = lean_unbox(v_severity_435_);
v_isSilent_boxed_441_ = lean_unbox(v_isSilent_436_);
v_res_442_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_433_, v_msgData_434_, v_severity_boxed_440_, v_isSilent_boxed_441_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v_ref_433_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(lean_object* v_ref_443_, lean_object* v_msgData_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = 1;
v___x_449_ = 0;
v___x_450_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_443_, v_msgData_444_, v___x_448_, v___x_449_, v___y_445_, v___y_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3___boxed(lean_object* v_ref_451_, lean_object* v_msgData_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_ref_451_, v_msgData_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_ref_451_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object* v_linterOption_463_, lean_object* v_stx_464_, lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_name_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_487_; 
v_name_469_ = lean_ctor_get(v_linterOption_463_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_linterOption_463_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_linterOption_463_, 1);
lean_dec(v_unused_488_);
v___x_471_ = v_linterOption_463_;
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_name_469_);
lean_dec(v_linterOption_463_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_487_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1);
lean_inc(v_name_469_);
v___x_474_ = l_Lean_MessageData_ofName(v_name_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 7);
lean_ctor_set(v___x_471_, 1, v___x_474_);
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_486_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_disable_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_477_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v_disable_479_ = l_Lean_MessageData_note(v___x_478_);
v___x_480_ = l_Lean_Linter_linterMessageTag;
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v_msg_465_);
lean_ctor_set(v___x_481_, 1, v_disable_479_);
v___x_482_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_483_, 0, v_name_469_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
lean_inc(v_stx_464_);
v___x_484_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_484_, 0, v_stx_464_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_stx_464_, v___x_484_, v___y_466_, v___y_467_);
lean_dec(v_stx_464_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object* v_linterOption_489_, lean_object* v_stx_490_, lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v_linterOption_489_, v_stx_490_, v_msg_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_495_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object* v___x_505_, uint8_t v___x_506_, lean_object* v___x_507_, lean_object* v_as_x27_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
if (lean_obj_tag(v_as_x27_508_) == 0)
{
lean_object* v___x_513_; 
lean_dec(v___x_507_);
lean_dec_ref(v___x_505_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_b_509_);
return v___x_513_;
}
else
{
lean_object* v_head_514_; lean_object* v_tail_515_; uint8_t v___x_516_; 
v_head_514_ = lean_ctor_get(v_as_x27_508_, 0);
v_tail_515_ = lean_ctor_get(v_as_x27_508_, 1);
v___x_516_ = l_Lean_NameSet_contains(v_b_509_, v_head_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
lean_inc_n(v_head_514_, 2);
v___x_517_ = l_Lean_NameSet_insert(v_b_509_, v_head_514_);
lean_inc_ref(v___x_505_);
v___x_518_ = l_Lean_Environment_contains(v___x_505_, v_head_514_, v___x_506_);
if (v___x_518_ == 0)
{
v_as_x27_508_ = v_tail_515_;
v_b_509_ = v___x_517_;
goto _start;
}
else
{
uint8_t v___x_520_; 
v___x_520_ = l_Lean_Linter_InternalModule_isInternalDecl(v_head_514_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Elab_Command_getRef___redArg(v___y_510_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_524_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1);
lean_inc(v_head_514_);
v___x_525_ = l_Lean_MessageData_ofConstName(v_head_514_, v___x_520_);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
lean_inc(v___x_507_);
v___x_529_ = l_Lean_MessageData_ofName(v___x_507_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v___x_523_, v_a_522_, v___x_532_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v_as_x27_508_ = v_tail_515_;
v_b_509_ = v___x_517_;
goto _start;
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v___x_517_);
lean_dec(v___x_507_);
lean_dec_ref(v___x_505_);
v_a_535_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v___x_517_);
lean_dec(v___x_507_);
lean_dec_ref(v___x_505_);
v_a_543_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_521_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_521_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
v_as_x27_508_ = v_tail_515_;
v_b_509_ = v___x_517_;
goto _start;
}
}
}
else
{
v_as_x27_508_ = v_tail_515_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v_as_x27_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_9582__boxed_561_; lean_object* v_res_562_; 
v___x_9582__boxed_561_ = lean_unbox(v___x_554_);
v_res_562_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_553_, v___x_9582__boxed_561_, v___x_555_, v_as_x27_556_, v_b_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v_as_x27_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object* v___x_563_, uint8_t v___x_564_, lean_object* v___x_565_, lean_object* v_as_566_, size_t v_sz_567_, size_t v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_lt(v_i_568_, v_sz_567_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec(v___x_565_);
lean_dec_ref(v___x_563_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v_b_569_);
return v___x_574_;
}
else
{
lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_598_; 
v_snd_575_ = lean_ctor_get(v_b_569_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_b_569_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_b_569_, 0);
lean_dec(v_unused_599_);
v___x_577_ = v_b_569_;
v_isShared_578_ = v_isSharedCheck_598_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_dec(v_b_569_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_598_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_a_579_ = lean_array_uget_borrowed(v_as_566_, v_i_568_);
lean_inc(v_a_579_);
v___x_580_ = l_Lean_Linter_getNewDecls(v_a_579_);
lean_inc(v___x_565_);
lean_inc_ref(v___x_563_);
v___x_581_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_563_, v___x_564_, v___x_565_, v___x_580_, v_snd_575_, v___y_570_, v___y_571_);
lean_dec(v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_box(0);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_a_582_);
lean_ctor_set(v___x_577_, 0, v___x_583_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_a_582_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
size_t v___x_586_; size_t v___x_587_; 
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_i_568_, v___x_586_);
v_i_568_ = v___x_587_;
v_b_569_ = v___x_585_;
goto _start;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_del_object(v___x_577_);
lean_dec(v___x_565_);
lean_dec_ref(v___x_563_);
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v_as_603_, lean_object* v_sz_604_, lean_object* v_i_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v___x_9690__boxed_610_; size_t v_sz_boxed_611_; size_t v_i_boxed_612_; lean_object* v_res_613_; 
v___x_9690__boxed_610_ = lean_unbox(v___x_601_);
v_sz_boxed_611_ = lean_unbox_usize(v_sz_604_);
lean_dec(v_sz_604_);
v_i_boxed_612_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_600_, v___x_9690__boxed_610_, v___x_602_, v_as_603_, v_sz_boxed_611_, v_i_boxed_612_, v_b_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec_ref(v_as_603_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object* v___x_614_, uint8_t v___x_615_, lean_object* v___x_616_, lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; 
lean_dec(v___x_616_);
lean_dec_ref(v___x_614_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_b_620_);
return v___x_625_;
}
else
{
lean_object* v_snd_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_649_; 
v_snd_626_ = lean_ctor_get(v_b_620_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_b_620_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_b_620_, 0);
lean_dec(v_unused_650_);
v___x_628_ = v_b_620_;
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snd_626_);
lean_dec(v_b_620_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_a_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_a_630_ = lean_array_uget_borrowed(v_as_617_, v_i_619_);
lean_inc(v_a_630_);
v___x_631_ = l_Lean_Linter_getNewDecls(v_a_630_);
lean_inc(v___x_616_);
lean_inc_ref(v___x_614_);
v___x_632_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_614_, v___x_615_, v___x_616_, v___x_631_, v_snd_626_, v___y_621_, v___y_622_);
lean_dec(v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_box(0);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_a_633_);
lean_ctor_set(v___x_628_, 0, v___x_634_);
v___x_636_ = v___x_628_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_a_633_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_619_, v___x_637_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_614_, v___x_615_, v___x_616_, v_as_617_, v_sz_618_, v___x_638_, v___x_636_, v___y_621_, v___y_622_);
return v___x_639_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_628_);
lean_dec(v___x_616_);
lean_dec_ref(v___x_614_);
v_a_641_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_632_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_632_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_as_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v___x_9758__boxed_661_; size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v___x_9758__boxed_661_ = lean_unbox(v___x_652_);
v_sz_boxed_662_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_663_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_651_, v___x_9758__boxed_661_, v___x_653_, v_as_654_, v_sz_boxed_662_, v_i_boxed_663_, v_b_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_as_654_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object* v___x_665_, uint8_t v___x_666_, lean_object* v___x_667_, lean_object* v_as_668_, size_t v_sz_669_, size_t v_i_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v___x_667_);
lean_dec_ref(v___x_665_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_671_);
return v___x_676_;
}
else
{
lean_object* v_snd_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_700_; 
v_snd_677_ = lean_ctor_get(v_b_671_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_b_671_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_b_671_, 0);
lean_dec(v_unused_701_);
v___x_679_ = v_b_671_;
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snd_677_);
lean_dec(v_b_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_a_681_ = lean_array_uget_borrowed(v_as_668_, v_i_670_);
lean_inc(v_a_681_);
v___x_682_ = l_Lean_Linter_getNewDecls(v_a_681_);
lean_inc(v___x_667_);
lean_inc_ref(v___x_665_);
v___x_683_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_665_, v___x_666_, v___x_667_, v___x_682_, v_snd_677_, v___y_672_, v___y_673_);
lean_dec(v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = lean_box(0);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v_a_684_);
lean_ctor_set(v___x_679_, 0, v___x_685_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_a_684_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
size_t v___x_688_; size_t v___x_689_; 
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_670_, v___x_688_);
v_i_670_ = v___x_689_;
v_b_671_ = v___x_687_;
goto _start;
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_679_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_665_);
v_a_692_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_683_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v_as_705_, lean_object* v_sz_706_, lean_object* v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___x_9826__boxed_712_; size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v___x_9826__boxed_712_ = lean_unbox(v___x_703_);
v_sz_boxed_713_ = lean_unbox_usize(v_sz_706_);
lean_dec(v_sz_706_);
v_i_boxed_714_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_702_, v___x_9826__boxed_712_, v___x_704_, v_as_705_, v_sz_boxed_713_, v_i_boxed_714_, v_b_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v_as_705_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object* v___x_716_, uint8_t v___x_717_, lean_object* v___x_718_, lean_object* v_as_719_, size_t v_sz_720_, size_t v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_721_, v_sz_720_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v___x_718_);
lean_dec_ref(v___x_716_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_722_);
return v___x_727_;
}
else
{
lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_751_; 
v_snd_728_ = lean_ctor_get(v_b_722_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_b_722_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v_b_722_, 0);
lean_dec(v_unused_752_);
v___x_730_ = v_b_722_;
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_dec(v_b_722_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_a_732_ = lean_array_uget_borrowed(v_as_719_, v_i_721_);
lean_inc(v_a_732_);
v___x_733_ = l_Lean_Linter_getNewDecls(v_a_732_);
lean_inc(v___x_718_);
lean_inc_ref(v___x_716_);
v___x_734_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_716_, v___x_717_, v___x_718_, v___x_733_, v_snd_728_, v___y_723_, v___y_724_);
lean_dec(v___x_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_a_735_);
lean_ctor_set(v___x_730_, 0, v___x_736_);
v___x_738_ = v___x_730_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_735_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_721_, v___x_739_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_716_, v___x_717_, v___x_718_, v_as_719_, v_sz_720_, v___x_740_, v___x_738_, v___y_723_, v___y_724_);
return v___x_741_;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_del_object(v___x_730_);
lean_dec(v___x_718_);
lean_dec_ref(v___x_716_);
v_a_743_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_734_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_734_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v___x_755_, lean_object* v_as_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_9894__boxed_763_; size_t v_sz_boxed_764_; size_t v_i_boxed_765_; lean_object* v_res_766_; 
v___x_9894__boxed_763_ = lean_unbox(v___x_754_);
v_sz_boxed_764_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_765_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_753_, v___x_9894__boxed_763_, v___x_755_, v_as_756_, v_sz_boxed_764_, v_i_boxed_765_, v_b_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_as_756_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object* v_init_767_, lean_object* v___x_768_, uint8_t v___x_769_, lean_object* v___x_770_, lean_object* v_n_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
if (lean_obj_tag(v_n_771_) == 0)
{
lean_object* v_cs_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; 
v_cs_776_ = lean_ctor_get(v_n_771_, 0);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_b_772_);
v_sz_779_ = lean_array_size(v_cs_776_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_767_, v___x_768_, v___x_769_, v___x_770_, v_cs_776_, v_sz_779_, v___x_780_, v___x_778_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_796_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_796_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; 
v_fst_786_ = lean_ctor_get(v_a_782_, 0);
if (lean_obj_tag(v_fst_786_) == 0)
{
lean_object* v_snd_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v_snd_787_ = lean_ctor_get(v_a_782_, 1);
lean_inc(v_snd_787_);
lean_dec(v_a_782_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_snd_787_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
else
{
lean_object* v_val_792_; lean_object* v___x_794_; 
lean_inc_ref(v_fst_786_);
lean_dec(v_a_782_);
v_val_792_ = lean_ctor_get(v_fst_786_, 0);
lean_inc(v_val_792_);
lean_dec_ref_known(v_fst_786_, 1);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_val_792_);
v___x_794_ = v___x_784_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_val_792_);
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
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_781_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_781_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_vs_805_; lean_object* v___x_806_; lean_object* v___x_807_; size_t v_sz_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_vs_805_ = lean_ctor_get(v_n_771_, 0);
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v_b_772_);
v_sz_808_ = lean_array_size(v_vs_805_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_768_, v___x_769_, v___x_770_, v_vs_805_, v_sz_808_, v___x_809_, v___x_807_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_825_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_825_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_825_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_fst_815_; 
v_fst_815_ = lean_ctor_get(v_a_811_, 0);
if (lean_obj_tag(v_fst_815_) == 0)
{
lean_object* v_snd_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v_snd_816_ = lean_ctor_get(v_a_811_, 1);
lean_inc(v_snd_816_);
lean_dec(v_a_811_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_snd_816_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; 
lean_inc_ref(v_fst_815_);
lean_dec(v_a_811_);
v_val_821_ = lean_ctor_get(v_fst_815_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_fst_815_, 1);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v_val_821_);
v___x_823_ = v___x_813_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_val_821_);
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
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_810_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_810_);
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
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object* v_init_834_, lean_object* v___x_835_, uint8_t v___x_836_, lean_object* v___x_837_, lean_object* v_as_838_, size_t v_sz_839_, size_t v_i_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_lt(v_i_840_, v_sz_839_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v___x_837_);
lean_dec_ref(v___x_835_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_b_841_);
return v___x_846_;
}
else
{
lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_881_; 
v_snd_847_ = lean_ctor_get(v_b_841_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_b_841_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v_b_841_, 0);
lean_dec(v_unused_882_);
v___x_849_ = v_b_841_;
v_isShared_850_ = v_isSharedCheck_881_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_dec(v_b_841_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_881_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_array_uget_borrowed(v_as_838_, v_i_840_);
lean_inc(v_snd_847_);
lean_inc(v___x_837_);
lean_inc_ref(v___x_835_);
v___x_852_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_834_, v___x_835_, v___x_836_, v___x_837_, v_a_851_, v_snd_847_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_872_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_872_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_872_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_872_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v___x_837_);
lean_dec_ref(v___x_835_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_a_853_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_857_);
v___x_859_ = v___x_849_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_snd_847_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_847_);
v_a_864_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v_a_853_, 1);
v___x_865_ = lean_box(0);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v_a_864_);
lean_ctor_set(v___x_849_, 0, v___x_865_);
v___x_867_ = v___x_849_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_864_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
size_t v___x_868_; size_t v___x_869_; 
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_840_, v___x_868_);
v_i_840_ = v___x_869_;
v_b_841_ = v___x_867_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_del_object(v___x_849_);
lean_dec(v_snd_847_);
lean_dec(v___x_837_);
lean_dec_ref(v___x_835_);
v_a_873_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_852_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_852_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_as_887_, lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_b_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v___x_9962__boxed_894_; size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v___x_9962__boxed_894_ = lean_unbox(v___x_885_);
v_sz_boxed_895_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_896_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_883_, v___x_884_, v___x_9962__boxed_894_, v___x_886_, v_as_887_, v_sz_boxed_895_, v_i_boxed_896_, v_b_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v_as_887_);
lean_dec(v_init_883_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object* v_init_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v_n_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_9984__boxed_907_; lean_object* v_res_908_; 
v___x_9984__boxed_907_ = lean_unbox(v___x_900_);
v_res_908_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_898_, v___x_899_, v___x_9984__boxed_907_, v___x_901_, v_n_902_, v_b_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v_n_902_);
lean_dec(v_init_898_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object* v___x_909_, uint8_t v___x_910_, lean_object* v___x_911_, lean_object* v_t_912_, lean_object* v_init_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_root_917_; lean_object* v_tail_918_; lean_object* v___x_919_; 
v_root_917_ = lean_ctor_get(v_t_912_, 0);
v_tail_918_ = lean_ctor_get(v_t_912_, 1);
lean_inc(v___x_911_);
lean_inc_ref(v___x_909_);
lean_inc(v_init_913_);
v___x_919_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_913_, v___x_909_, v___x_910_, v___x_911_, v_root_917_, v_init_913_, v___y_914_, v___y_915_);
lean_dec(v_init_913_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_956_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_956_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_956_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_956_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
if (lean_obj_tag(v_a_920_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; 
lean_dec(v___x_911_);
lean_dec_ref(v___x_909_);
v_a_924_ = lean_ctor_get(v_a_920_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v_a_920_, 1);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_a_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; size_t v_sz_931_; size_t v___x_932_; lean_object* v___x_933_; 
lean_del_object(v___x_922_);
v_a_928_ = lean_ctor_get(v_a_920_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v_a_920_, 1);
v___x_929_ = lean_box(0);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_928_);
v_sz_931_ = lean_array_size(v_tail_918_);
v___x_932_ = ((size_t)0ULL);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_909_, v___x_910_, v___x_911_, v_tail_918_, v_sz_931_, v___x_932_, v___x_930_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_947_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_947_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_fst_938_; 
v_fst_938_ = lean_ctor_get(v_a_934_, 0);
if (lean_obj_tag(v_fst_938_) == 0)
{
lean_object* v_snd_939_; lean_object* v___x_941_; 
v_snd_939_ = lean_ctor_get(v_a_934_, 1);
lean_inc(v_snd_939_);
lean_dec(v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_snd_939_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_snd_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; 
lean_inc_ref(v_fst_938_);
lean_dec(v_a_934_);
v_val_943_ = lean_ctor_get(v_fst_938_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_fst_938_, 1);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_val_943_);
v___x_945_ = v___x_936_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_val_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_933_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_933_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v___x_911_);
lean_dec_ref(v___x_909_);
v_a_957_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_919_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_919_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v_t_968_, lean_object* v_init_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_10175__boxed_973_; lean_object* v_res_974_; 
v___x_10175__boxed_973_ = lean_unbox(v___x_966_);
v_res_974_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v___x_965_, v___x_10175__boxed_973_, v___x_967_, v_t_968_, v_init_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_t_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object* v_o_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v___x_980_; lean_object* v_toEnvExtension_981_; lean_object* v_asyncMode_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_merged_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_981_ = lean_ctor_get(v___x_980_, 0);
v_asyncMode_982_ = lean_ctor_get(v_toEnvExtension_981_, 2);
v___x_983_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_984_ = lean_box(0);
v___x_985_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_983_, v___x_980_, v_env_979_, v_asyncMode_982_, v___x_984_);
v_merged_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_985_, 1);
lean_dec(v_unused_995_);
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_merged_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v_merged_986_);
lean_ctor_set(v___x_988_, 0, v_o_975_);
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_o_975_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_merged_986_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_996_, v___y_997_);
lean_dec(v___y_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v_scopes_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_opts_1007_; lean_object* v___x_1008_; 
v___x_1003_ = lean_st_ref_get(v___y_1001_);
v_scopes_1004_ = lean_ctor_get(v___x_1003_, 2);
lean_inc(v_scopes_1004_);
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1006_ = l_List_head_x21___redArg(v___x_1005_, v_scopes_1004_);
lean_dec(v_scopes_1004_);
v_opts_1007_ = lean_ctor_get(v___x_1006_, 1);
lean_inc_ref(v_opts_1007_);
lean_dec(v___x_1006_);
v___x_1008_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_opts_1007_, v___y_1001_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v_messages_1018_; uint8_t v___x_1019_; 
v___x_1017_ = lean_st_ref_get(v___y_1015_);
v_messages_1018_ = lean_ctor_get(v___x_1017_, 1);
lean_inc_ref(v_messages_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Lean_MessageLog_hasErrors(v_messages_1018_);
lean_dec_ref(v_messages_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1060_; 
v___x_1020_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1014_, v___y_1015_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1060_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1060_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_1026_ = l_Lean_Linter_getLinterValue(v___x_1025_, v_a_1021_);
lean_dec(v_a_1021_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
lean_object* v___x_1031_; lean_object* v_env_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1031_ = lean_st_ref_get(v___y_1015_);
v_env_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc_ref(v_env_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Lean_Environment_mainModule(v_env_1032_);
v___x_1034_ = l_Lean_Linter_InternalModule_isInternalModule(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec(v___x_1033_);
lean_dec_ref(v_env_1032_);
v___x_1035_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1035_);
v___x_1037_ = v___x_1023_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_del_object(v___x_1023_);
v___x_1039_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_1015_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = l_Lean_NameSet_empty;
v___x_1042_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v_env_1032_, v___x_1034_, v___x_1033_, v_a_1040_, v___x_1041_, v___y_1014_, v___y_1015_);
lean_dec(v_a_1040_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1042_, 0);
lean_dec(v_unused_1051_);
v___x_1044_ = v___x_1042_;
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v___x_1042_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1050_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_box(0);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1042_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1042_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(v_x_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v_x_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object* v_o_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1082_, v___y_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object* v_o_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(v_o_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object* v___x_1092_, uint8_t v___x_1093_, lean_object* v___x_1094_, lean_object* v_as_1095_, lean_object* v_as_x27_1096_, lean_object* v_b_1097_, lean_object* v_a_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_1092_, v___x_1093_, v___x_1094_, v_as_x27_1096_, v_b_1097_, v___y_1099_, v___y_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v_as_1106_, lean_object* v_as_x27_1107_, lean_object* v_b_1108_, lean_object* v_a_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_10487__boxed_1113_; lean_object* v_res_1114_; 
v___x_10487__boxed_1113_ = lean_unbox(v___x_1104_);
v_res_1114_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(v___x_1103_, v___x_10487__boxed_1113_, v___x_1105_, v_as_1106_, v_as_x27_1107_, v_b_1108_, v_a_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v_as_x27_1107_);
lean_dec(v_as_1106_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_msgData_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_1115_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(v_msgData_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModuleLinter));
v___x_1127_ = l_Lean_Elab_Command_addLinter(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
return v_res_1129_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_InternalModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
