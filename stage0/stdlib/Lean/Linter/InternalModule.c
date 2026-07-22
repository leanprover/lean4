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
uint8_t v___y_9138__boxed_246_; uint8_t v_suppressElabErrors_boxed_247_; uint8_t v_res_248_; lean_object* v_r_249_; 
v___y_9138__boxed_246_ = lean_unbox(v___y_243_);
v_suppressElabErrors_boxed_247_ = lean_unbox(v_suppressElabErrors_244_);
v_res_248_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(v___y_9138__boxed_246_, v_suppressElabErrors_boxed_247_, v_x_245_);
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
lean_object* v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; uint8_t v___y_361_; uint8_t v___y_362_; uint8_t v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; uint8_t v___y_389_; lean_object* v___y_390_; uint8_t v___y_391_; uint8_t v___y_392_; lean_object* v___y_393_; uint8_t v___y_397_; uint8_t v___y_398_; uint8_t v___y_399_; uint8_t v___x_414_; uint8_t v___y_416_; uint8_t v___y_417_; uint8_t v___y_418_; uint8_t v___y_420_; uint8_t v___x_432_; 
v___x_414_ = 2;
v___x_432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_291_, v___x_414_);
if (v___x_432_ == 0)
{
v___y_420_ = v___x_432_;
goto v___jp_419_;
}
else
{
uint8_t v___x_433_; 
lean_inc_ref(v_msgData_290_);
v___x_433_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_290_);
v___y_420_ = v___x_433_;
goto v___jp_419_;
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
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_343_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_343_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_343_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_343_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_currNamespace_313_; lean_object* v_openDecls_314_; lean_object* v_env_315_; lean_object* v_messages_316_; lean_object* v_scopes_317_; lean_object* v_usedQuotCtxts_318_; lean_object* v_nextMacroScope_319_; lean_object* v_maxRecDepth_320_; lean_object* v_ngen_321_; lean_object* v_auxDeclNGen_322_; lean_object* v_infoState_323_; lean_object* v_traceState_324_; lean_object* v_snapshotTasks_325_; lean_object* v_prevLinterStates_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_342_; 
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
v_prevLinterStates_326_ = lean_ctor_get(v___x_312_, 11);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_342_ == 0)
{
v___x_328_ = v___x_312_;
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_prevLinterStates_326_);
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
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_currNamespace_313_);
lean_ctor_set(v___x_330_, 1, v_openDecls_314_);
v___x_331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___y_303_);
lean_inc_ref(v___y_297_);
lean_inc_ref(v___y_300_);
v___x_332_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_332_, 0, v___y_300_);
lean_ctor_set(v___x_332_, 1, v___y_302_);
lean_ctor_set(v___x_332_, 2, v___y_298_);
lean_ctor_set(v___x_332_, 3, v___y_297_);
lean_ctor_set(v___x_332_, 4, v___x_331_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*5, v___y_301_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*5 + 1, v___y_299_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*5 + 2, v_isSilent_292_);
v___x_333_ = l_Lean_MessageLog_add(v___x_332_, v_messages_316_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_env_315_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_scopes_317_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_usedQuotCtxts_318_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_nextMacroScope_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 5, v_maxRecDepth_320_);
lean_ctor_set(v_reuseFailAlloc_341_, 6, v_ngen_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 7, v_auxDeclNGen_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 8, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_341_, 9, v_traceState_324_);
lean_ctor_set(v_reuseFailAlloc_341_, 10, v_snapshotTasks_325_);
lean_ctor_set(v_reuseFailAlloc_341_, 11, v_prevLinterStates_326_);
v___x_335_ = v_reuseFailAlloc_341_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_st_ref_set(v___y_304_, v___x_335_);
v___x_337_ = lean_box(0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_337_);
v___x_339_ = v___x_310_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_306_);
lean_dec_ref(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_298_);
v_a_344_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_307_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_307_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_298_);
v_a_352_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_305_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_305_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
v___jp_360_:
{
lean_object* v_fileName_366_; lean_object* v_fileMap_367_; uint8_t v_suppressElabErrors_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_387_; 
v_fileName_366_ = lean_ctor_get(v___y_293_, 0);
v_fileMap_367_ = lean_ctor_get(v___y_293_, 1);
v_suppressElabErrors_368_ = lean_ctor_get_uint8(v___y_293_, sizeof(void*)*10);
v___x_369_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_290_);
v___x_370_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v___x_369_, v___y_294_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_inc_ref_n(v_fileMap_367_, 2);
v___x_375_ = l_Lean_FileMap_toPosition(v_fileMap_367_, v___y_364_);
lean_dec(v___y_364_);
v___x_376_ = l_Lean_FileMap_toPosition(v_fileMap_367_, v___y_365_);
lean_dec(v___y_365_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___x_378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0));
if (v_suppressElabErrors_368_ == 0)
{
lean_del_object(v___x_373_);
v___y_297_ = v___x_378_;
v___y_298_ = v___x_377_;
v___y_299_ = v___y_362_;
v___y_300_ = v_fileName_366_;
v___y_301_ = v___y_363_;
v___y_302_ = v___x_375_;
v___y_303_ = v_a_371_;
v___y_304_ = v___y_294_;
goto v___jp_296_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___f_381_; uint8_t v___x_382_; 
v___x_379_ = lean_box(v___y_361_);
v___x_380_ = lean_box(v_suppressElabErrors_368_);
v___f_381_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_381_, 0, v___x_379_);
lean_closure_set(v___f_381_, 1, v___x_380_);
lean_inc(v_a_371_);
v___x_382_ = l_Lean_MessageData_hasTag(v___f_381_, v_a_371_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec_ref_known(v___x_377_, 1);
lean_dec_ref(v___x_375_);
lean_dec(v_a_371_);
v___x_383_ = lean_box(0);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_383_);
v___x_385_ = v___x_373_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_del_object(v___x_373_);
v___y_297_ = v___x_378_;
v___y_298_ = v___x_377_;
v___y_299_ = v___y_362_;
v___y_300_ = v_fileName_366_;
v___y_301_ = v___y_363_;
v___y_302_ = v___x_375_;
v___y_303_ = v_a_371_;
v___y_304_ = v___y_294_;
goto v___jp_296_;
}
}
}
}
v___jp_388_:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Syntax_getTailPos_x3f(v___y_390_, v___y_392_);
lean_dec(v___y_390_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_inc(v___y_393_);
v___y_361_ = v___y_389_;
v___y_362_ = v___y_391_;
v___y_363_ = v___y_392_;
v___y_364_ = v___y_393_;
v___y_365_ = v___y_393_;
goto v___jp_360_;
}
else
{
lean_object* v_val_395_; 
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_394_, 1);
v___y_361_ = v___y_389_;
v___y_362_ = v___y_391_;
v___y_363_ = v___y_392_;
v___y_364_ = v___y_393_;
v___y_365_ = v_val_395_;
goto v___jp_360_;
}
}
v___jp_396_:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Elab_Command_getRef___redArg(v___y_293_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_ref_402_; lean_object* v___x_403_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v_ref_402_ = l_Lean_replaceRef(v_ref_289_, v_a_401_);
lean_dec(v_a_401_);
v___x_403_ = l_Lean_Syntax_getPos_x3f(v_ref_402_, v___y_398_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___y_389_ = v___y_397_;
v___y_390_ = v_ref_402_;
v___y_391_ = v___y_399_;
v___y_392_ = v___y_398_;
v___y_393_ = v___x_404_;
goto v___jp_388_;
}
else
{
lean_object* v_val_405_; 
v_val_405_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_403_, 1);
v___y_389_ = v___y_397_;
v___y_390_ = v_ref_402_;
v___y_391_ = v___y_399_;
v___y_392_ = v___y_398_;
v___y_393_ = v_val_405_;
goto v___jp_388_;
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v_msgData_290_);
v_a_406_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_400_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
v___jp_415_:
{
if (v___y_418_ == 0)
{
v___y_397_ = v___y_416_;
v___y_398_ = v___y_417_;
v___y_399_ = v_severity_291_;
goto v___jp_396_;
}
else
{
v___y_397_ = v___y_416_;
v___y_398_ = v___y_417_;
v___y_399_ = v___x_414_;
goto v___jp_396_;
}
}
v___jp_419_:
{
if (v___y_420_ == 0)
{
lean_object* v___x_421_; lean_object* v_scopes_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_opts_425_; uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_421_ = lean_st_ref_get(v___y_294_);
v_scopes_422_ = lean_ctor_get(v___x_421_, 2);
lean_inc(v_scopes_422_);
lean_dec(v___x_421_);
v___x_423_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_424_ = l_List_head_x21___redArg(v___x_423_, v_scopes_422_);
lean_dec(v_scopes_422_);
v_opts_425_ = lean_ctor_get(v___x_424_, 1);
lean_inc_ref(v_opts_425_);
lean_dec(v___x_424_);
v___x_426_ = 1;
v___x_427_ = l_Lean_instBEqMessageSeverity_beq(v_severity_291_, v___x_426_);
if (v___x_427_ == 0)
{
lean_dec_ref(v_opts_425_);
v___y_416_ = v___y_420_;
v___y_417_ = v___y_420_;
v___y_418_ = v___x_427_;
goto v___jp_415_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = l_Lean_warningAsError;
v___x_429_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_425_, v___x_428_);
lean_dec_ref(v_opts_425_);
v___y_416_ = v___y_420_;
v___y_417_ = v___y_420_;
v___y_418_ = v___x_429_;
goto v___jp_415_;
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_msgData_290_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_434_, lean_object* v_msgData_435_, lean_object* v_severity_436_, lean_object* v_isSilent_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_severity_boxed_441_; uint8_t v_isSilent_boxed_442_; lean_object* v_res_443_; 
v_severity_boxed_441_ = lean_unbox(v_severity_436_);
v_isSilent_boxed_442_ = lean_unbox(v_isSilent_437_);
v_res_443_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_434_, v_msgData_435_, v_severity_boxed_441_, v_isSilent_boxed_442_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_ref_434_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(lean_object* v_ref_444_, lean_object* v_msgData_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = 1;
v___x_450_ = 0;
v___x_451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_444_, v_msgData_445_, v___x_449_, v___x_450_, v___y_446_, v___y_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3___boxed(lean_object* v_ref_452_, lean_object* v_msgData_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_ref_452_, v_msgData_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_ref_452_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object* v_linterOption_464_, lean_object* v_stx_465_, lean_object* v_msg_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_name_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_488_; 
v_name_470_ = lean_ctor_get(v_linterOption_464_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_linterOption_464_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; 
v_unused_489_ = lean_ctor_get(v_linterOption_464_, 1);
lean_dec(v_unused_489_);
v___x_472_ = v_linterOption_464_;
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_name_470_);
lean_dec(v_linterOption_464_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_488_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1);
lean_inc(v_name_470_);
v___x_475_ = l_Lean_MessageData_ofName(v_name_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 7);
lean_ctor_set(v___x_472_, 1, v___x_475_);
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_487_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_disable_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_478_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v_disable_480_ = l_Lean_MessageData_note(v___x_479_);
v___x_481_ = l_Lean_Linter_linterMessageTag;
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v_msg_466_);
lean_ctor_set(v___x_482_, 1, v_disable_480_);
v___x_483_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_484_, 0, v_name_470_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
lean_inc(v_stx_465_);
v___x_485_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_485_, 0, v_stx_465_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_stx_465_, v___x_485_, v___y_467_, v___y_468_);
lean_dec(v_stx_465_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object* v_linterOption_490_, lean_object* v_stx_491_, lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v_linterOption_490_, v_stx_491_, v_msg_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
return v_res_496_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object* v___x_506_, uint8_t v___x_507_, lean_object* v___x_508_, lean_object* v_as_x27_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
if (lean_obj_tag(v_as_x27_509_) == 0)
{
lean_object* v___x_514_; 
lean_dec(v___x_508_);
lean_dec_ref(v___x_506_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_b_510_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; uint8_t v___x_517_; 
v_head_515_ = lean_ctor_get(v_as_x27_509_, 0);
v_tail_516_ = lean_ctor_get(v_as_x27_509_, 1);
v___x_517_ = l_Lean_NameSet_contains(v_b_510_, v_head_515_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
lean_inc_n(v_head_515_, 2);
v___x_518_ = l_Lean_NameSet_insert(v_b_510_, v_head_515_);
lean_inc_ref(v___x_506_);
v___x_519_ = l_Lean_Environment_contains(v___x_506_, v_head_515_, v___x_507_);
if (v___x_519_ == 0)
{
v_as_x27_509_ = v_tail_516_;
v_b_510_ = v___x_518_;
goto _start;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_Linter_InternalModule_isInternalDecl(v_head_515_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_Command_getRef___redArg(v___y_511_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_525_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1);
lean_inc(v_head_515_);
v___x_526_ = l_Lean_MessageData_ofConstName(v_head_515_, v___x_521_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_inc(v___x_508_);
v___x_530_ = l_Lean_MessageData_ofName(v___x_508_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v___x_524_, v_a_523_, v___x_533_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_dec_ref_known(v___x_534_, 1);
v_as_x27_509_ = v_tail_516_;
v_b_510_ = v___x_518_;
goto _start;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v___x_518_);
lean_dec(v___x_508_);
lean_dec_ref(v___x_506_);
v_a_536_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_534_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec(v___x_518_);
lean_dec(v___x_508_);
lean_dec_ref(v___x_506_);
v_a_544_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_522_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_522_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
v_as_x27_509_ = v_tail_516_;
v_b_510_ = v___x_518_;
goto _start;
}
}
}
else
{
v_as_x27_509_ = v_tail_516_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v_as_x27_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_9602__boxed_562_; lean_object* v_res_563_; 
v___x_9602__boxed_562_ = lean_unbox(v___x_555_);
v_res_563_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_554_, v___x_9602__boxed_562_, v___x_556_, v_as_x27_557_, v_b_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v_as_x27_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object* v___x_564_, uint8_t v___x_565_, lean_object* v___x_566_, lean_object* v_as_567_, size_t v_sz_568_, size_t v_i_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_566_);
lean_dec_ref(v___x_564_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_b_570_);
return v___x_575_;
}
else
{
lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_599_; 
v_snd_576_ = lean_ctor_get(v_b_570_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_b_570_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_b_570_, 0);
lean_dec(v_unused_600_);
v___x_578_ = v_b_570_;
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_dec(v_b_570_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_580_ = lean_array_uget_borrowed(v_as_567_, v_i_569_);
lean_inc(v_a_580_);
v___x_581_ = l_Lean_Linter_getNewDecls(v_a_580_);
lean_inc(v___x_566_);
lean_inc_ref(v___x_564_);
v___x_582_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_564_, v___x_565_, v___x_566_, v___x_581_, v_snd_576_, v___y_571_, v___y_572_);
lean_dec(v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_box(0);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_a_583_);
lean_ctor_set(v___x_578_, 0, v___x_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_583_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
size_t v___x_587_; size_t v___x_588_; 
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_569_, v___x_587_);
v_i_569_ = v___x_588_;
v_b_570_ = v___x_586_;
goto _start;
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_del_object(v___x_578_);
lean_dec(v___x_566_);
lean_dec_ref(v___x_564_);
v_a_591_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_582_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v_as_604_, lean_object* v_sz_605_, lean_object* v_i_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v___x_9710__boxed_611_; size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v___x_9710__boxed_611_ = lean_unbox(v___x_602_);
v_sz_boxed_612_ = lean_unbox_usize(v_sz_605_);
lean_dec(v_sz_605_);
v_i_boxed_613_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_601_, v___x_9710__boxed_611_, v___x_603_, v_as_604_, v_sz_boxed_612_, v_i_boxed_613_, v_b_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_as_604_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object* v___x_615_, uint8_t v___x_616_, lean_object* v___x_617_, lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v___x_617_);
lean_dec_ref(v___x_615_);
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
lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_a_631_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
lean_inc(v_a_631_);
v___x_632_ = l_Lean_Linter_getNewDecls(v_a_631_);
lean_inc(v___x_617_);
lean_inc_ref(v___x_615_);
v___x_633_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_615_, v___x_616_, v___x_617_, v___x_632_, v_snd_627_, v___y_622_, v___y_623_);
lean_dec(v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = lean_box(0);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_a_634_);
lean_ctor_set(v___x_629_, 0, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_a_634_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_620_, v___x_638_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_615_, v___x_616_, v___x_617_, v_as_618_, v_sz_619_, v___x_639_, v___x_637_, v___y_622_, v___y_623_);
return v___x_640_;
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_del_object(v___x_629_);
lean_dec(v___x_617_);
lean_dec_ref(v___x_615_);
v_a_642_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_633_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v_as_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v___x_9778__boxed_662_; size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v___x_9778__boxed_662_ = lean_unbox(v___x_653_);
v_sz_boxed_663_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_664_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_652_, v___x_9778__boxed_662_, v___x_654_, v_as_655_, v_sz_boxed_663_, v_i_boxed_664_, v_b_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v_as_655_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object* v___x_666_, uint8_t v___x_667_, lean_object* v___x_668_, lean_object* v_as_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_668_);
lean_dec_ref(v___x_666_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_b_672_);
return v___x_677_;
}
else
{
lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_701_; 
v_snd_678_ = lean_ctor_get(v_b_672_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_b_672_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_b_672_, 0);
lean_dec(v_unused_702_);
v___x_680_ = v_b_672_;
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_dec(v_b_672_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_a_682_ = lean_array_uget_borrowed(v_as_669_, v_i_671_);
lean_inc(v_a_682_);
v___x_683_ = l_Lean_Linter_getNewDecls(v_a_682_);
lean_inc(v___x_668_);
lean_inc_ref(v___x_666_);
v___x_684_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_666_, v___x_667_, v___x_668_, v___x_683_, v_snd_678_, v___y_673_, v___y_674_);
lean_dec(v___x_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v_a_685_);
lean_ctor_set(v___x_680_, 0, v___x_686_);
v___x_688_ = v___x_680_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_685_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
size_t v___x_689_; size_t v___x_690_; 
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_671_, v___x_689_);
v_i_671_ = v___x_690_;
v_b_672_ = v___x_688_;
goto _start;
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_del_object(v___x_680_);
lean_dec(v___x_668_);
lean_dec_ref(v___x_666_);
v_a_693_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_684_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_684_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_as_706_, lean_object* v_sz_707_, lean_object* v_i_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_9846__boxed_713_; size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v___x_9846__boxed_713_ = lean_unbox(v___x_704_);
v_sz_boxed_714_ = lean_unbox_usize(v_sz_707_);
lean_dec(v_sz_707_);
v_i_boxed_715_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_703_, v___x_9846__boxed_713_, v___x_705_, v_as_706_, v_sz_boxed_714_, v_i_boxed_715_, v_b_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_as_706_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object* v___x_717_, uint8_t v___x_718_, lean_object* v___x_719_, lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v___x_719_);
lean_dec_ref(v___x_717_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_723_);
return v___x_728_;
}
else
{
lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_752_; 
v_snd_729_ = lean_ctor_get(v_b_723_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_b_723_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_b_723_, 0);
lean_dec(v_unused_753_);
v___x_731_ = v_b_723_;
v_isShared_732_ = v_isSharedCheck_752_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_dec(v_b_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_752_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_733_ = lean_array_uget_borrowed(v_as_720_, v_i_722_);
lean_inc(v_a_733_);
v___x_734_ = l_Lean_Linter_getNewDecls(v_a_733_);
lean_inc(v___x_719_);
lean_inc_ref(v___x_717_);
v___x_735_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_717_, v___x_718_, v___x_719_, v___x_734_, v_snd_729_, v___y_724_, v___y_725_);
lean_dec(v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_a_736_);
lean_ctor_set(v___x_731_, 0, v___x_737_);
v___x_739_ = v___x_731_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_a_736_);
v___x_739_ = v_reuseFailAlloc_743_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_add(v_i_722_, v___x_740_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_717_, v___x_718_, v___x_719_, v_as_720_, v_sz_721_, v___x_741_, v___x_739_, v___y_724_, v___y_725_);
return v___x_742_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_731_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_717_);
v_a_744_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_735_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_735_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_754_, lean_object* v___x_755_, lean_object* v___x_756_, lean_object* v_as_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_9914__boxed_764_; size_t v_sz_boxed_765_; size_t v_i_boxed_766_; lean_object* v_res_767_; 
v___x_9914__boxed_764_ = lean_unbox(v___x_755_);
v_sz_boxed_765_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_766_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_754_, v___x_9914__boxed_764_, v___x_756_, v_as_757_, v_sz_boxed_765_, v_i_boxed_766_, v_b_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v_as_757_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object* v_init_768_, lean_object* v___x_769_, uint8_t v___x_770_, lean_object* v___x_771_, lean_object* v_n_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
if (lean_obj_tag(v_n_772_) == 0)
{
lean_object* v_cs_777_; lean_object* v___x_778_; lean_object* v___x_779_; size_t v_sz_780_; size_t v___x_781_; lean_object* v___x_782_; 
v_cs_777_ = lean_ctor_get(v_n_772_, 0);
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_b_773_);
v_sz_780_ = lean_array_size(v_cs_777_);
v___x_781_ = ((size_t)0ULL);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_768_, v___x_769_, v___x_770_, v___x_771_, v_cs_777_, v_sz_780_, v___x_781_, v___x_779_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_797_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
if (lean_obj_tag(v_fst_787_) == 0)
{
lean_object* v_snd_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v_snd_788_ = lean_ctor_get(v_a_783_, 1);
lean_inc(v_snd_788_);
lean_dec(v_a_783_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_snd_788_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; 
lean_inc_ref(v_fst_787_);
lean_dec(v_a_783_);
v_val_793_ = lean_ctor_get(v_fst_787_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_fst_787_, 1);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_val_793_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_val_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_782_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_782_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_vs_806_; lean_object* v___x_807_; lean_object* v___x_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_vs_806_ = lean_ctor_get(v_n_772_, 0);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v_b_773_);
v_sz_809_ = lean_array_size(v_vs_806_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_769_, v___x_770_, v___x_771_, v_vs_806_, v_sz_809_, v___x_810_, v___x_808_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_826_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_826_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_826_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_826_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_fst_816_; 
v_fst_816_ = lean_ctor_get(v_a_812_, 0);
if (lean_obj_tag(v_fst_816_) == 0)
{
lean_object* v_snd_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_snd_817_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_snd_817_);
lean_dec(v_a_812_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_snd_817_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_818_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; 
lean_inc_ref(v_fst_816_);
lean_dec(v_a_812_);
v_val_822_ = lean_ctor_get(v_fst_816_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_fst_816_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_val_822_);
v___x_824_ = v___x_814_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_val_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_811_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_811_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object* v_init_835_, lean_object* v___x_836_, uint8_t v___x_837_, lean_object* v___x_838_, lean_object* v_as_839_, size_t v_sz_840_, size_t v_i_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_841_, v_sz_840_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v___x_838_);
lean_dec_ref(v___x_836_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_842_);
return v___x_847_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_882_; 
v_snd_848_ = lean_ctor_get(v_b_842_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_b_842_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_b_842_, 0);
lean_dec(v_unused_883_);
v___x_850_ = v_b_842_;
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_842_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_array_uget_borrowed(v_as_839_, v_i_841_);
lean_inc(v_snd_848_);
lean_inc(v___x_838_);
lean_inc_ref(v___x_836_);
v___x_853_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_835_, v___x_836_, v___x_837_, v___x_838_, v_a_852_, v_snd_848_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_873_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_873_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v___x_838_);
lean_dec_ref(v___x_836_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_a_854_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_848_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_848_);
v_a_865_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v_a_854_, 1);
v___x_866_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_865_);
lean_ctor_set(v___x_850_, 0, v___x_866_);
v___x_868_ = v___x_850_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_865_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
size_t v___x_869_; size_t v___x_870_; 
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_841_, v___x_869_);
v_i_841_ = v___x_870_;
v_b_842_ = v___x_868_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
lean_dec(v___x_838_);
lean_dec_ref(v___x_836_);
v_a_874_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_853_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_853_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_884_, lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v_as_888_, lean_object* v_sz_889_, lean_object* v_i_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_9982__boxed_895_; size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v___x_9982__boxed_895_ = lean_unbox(v___x_886_);
v_sz_boxed_896_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_i_boxed_897_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_884_, v___x_885_, v___x_9982__boxed_895_, v___x_887_, v_as_888_, v_sz_boxed_896_, v_i_boxed_897_, v_b_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_as_888_);
lean_dec(v_init_884_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object* v_init_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v_n_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v___x_10004__boxed_908_; lean_object* v_res_909_; 
v___x_10004__boxed_908_ = lean_unbox(v___x_901_);
v_res_909_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_899_, v___x_900_, v___x_10004__boxed_908_, v___x_902_, v_n_903_, v_b_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec_ref(v_n_903_);
lean_dec(v_init_899_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object* v___x_910_, uint8_t v___x_911_, lean_object* v___x_912_, lean_object* v_t_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_root_918_; lean_object* v_tail_919_; lean_object* v___x_920_; 
v_root_918_ = lean_ctor_get(v_t_913_, 0);
v_tail_919_ = lean_ctor_get(v_t_913_, 1);
lean_inc(v___x_912_);
lean_inc_ref(v___x_910_);
lean_inc(v_init_914_);
v___x_920_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_914_, v___x_910_, v___x_911_, v___x_912_, v_root_918_, v_init_914_, v___y_915_, v___y_916_);
lean_dec(v_init_914_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_957_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_957_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_957_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_957_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; 
lean_dec(v___x_912_);
lean_dec_ref(v___x_910_);
v_a_925_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v_a_921_, 1);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v_a_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_925_);
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
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; 
lean_del_object(v___x_923_);
v_a_929_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v_a_921_, 1);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_a_929_);
v_sz_932_ = lean_array_size(v_tail_919_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_910_, v___x_911_, v___x_912_, v_tail_919_, v_sz_932_, v___x_933_, v___x_931_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_948_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_948_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_fst_939_; 
v_fst_939_ = lean_ctor_get(v_a_935_, 0);
if (lean_obj_tag(v_fst_939_) == 0)
{
lean_object* v_snd_940_; lean_object* v___x_942_; 
v_snd_940_ = lean_ctor_get(v_a_935_, 1);
lean_inc(v_snd_940_);
lean_dec(v_a_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_snd_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_snd_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
lean_object* v_val_944_; lean_object* v___x_946_; 
lean_inc_ref(v_fst_939_);
lean_dec(v_a_935_);
v_val_944_ = lean_ctor_get(v_fst_939_, 0);
lean_inc(v_val_944_);
lean_dec_ref_known(v_fst_939_, 1);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_val_944_);
v___x_946_ = v___x_937_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_val_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_934_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_934_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v___x_912_);
lean_dec_ref(v___x_910_);
v_a_958_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_920_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_920_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
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
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v_t_969_, lean_object* v_init_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v___x_10195__boxed_974_; lean_object* v_res_975_; 
v___x_10195__boxed_974_ = lean_unbox(v___x_967_);
v_res_975_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v___x_966_, v___x_10195__boxed_974_, v___x_968_, v_t_969_, v_init_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_t_969_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object* v_o_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v_env_980_; lean_object* v___x_981_; lean_object* v_toEnvExtension_982_; lean_object* v_asyncMode_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_merged_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v___x_979_ = lean_st_ref_get(v___y_977_);
v_env_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc_ref(v_env_980_);
lean_dec(v___x_979_);
v___x_981_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_982_ = lean_ctor_get(v___x_981_, 0);
v_asyncMode_983_ = lean_ctor_get(v_toEnvExtension_982_, 2);
v___x_984_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_985_ = lean_box(0);
v___x_986_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_984_, v___x_981_, v_env_980_, v_asyncMode_983_, v___x_985_);
v_merged_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_986_, 1);
lean_dec(v_unused_996_);
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_merged_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v_merged_987_);
lean_ctor_set(v___x_989_, 0, v_o_976_);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_o_976_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_merged_987_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_997_, v___y_998_);
lean_dec(v___y_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_scopes_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_opts_1008_; lean_object* v___x_1009_; 
v___x_1004_ = lean_st_ref_get(v___y_1002_);
v_scopes_1005_ = lean_ctor_get(v___x_1004_, 2);
lean_inc(v_scopes_1005_);
lean_dec(v___x_1004_);
v___x_1006_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1007_ = l_List_head_x21___redArg(v___x_1006_, v_scopes_1005_);
lean_dec(v_scopes_1005_);
v_opts_1008_ = lean_ctor_get(v___x_1007_, 1);
lean_inc_ref(v_opts_1008_);
lean_dec(v___x_1007_);
v___x_1009_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_opts_1008_, v___y_1002_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v_messages_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_st_ref_get(v___y_1016_);
v_messages_1019_ = lean_ctor_get(v___x_1018_, 1);
lean_inc_ref(v_messages_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Lean_MessageLog_hasErrors(v_messages_1019_);
lean_dec_ref(v_messages_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1061_; 
v___x_1021_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1015_, v___y_1016_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_1027_ = l_Lean_Linter_getLinterValue(v___x_1026_, v_a_1022_);
lean_dec(v_a_1022_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v_env_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1032_ = lean_st_ref_get(v___y_1016_);
v_env_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_env_1033_);
lean_dec(v___x_1032_);
v___x_1034_ = l_Lean_Environment_mainModule(v_env_1033_);
v___x_1035_ = l_Lean_Linter_InternalModule_isInternalModule(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec(v___x_1034_);
lean_dec_ref(v_env_1033_);
v___x_1036_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1036_);
v___x_1038_ = v___x_1024_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_del_object(v___x_1024_);
v___x_1040_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_1016_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = l_Lean_NameSet_empty;
v___x_1043_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v_env_1033_, v___x_1035_, v___x_1034_, v_a_1041_, v___x_1042_, v___y_1015_, v___y_1016_);
lean_dec(v_a_1041_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___x_1043_, 0);
lean_dec(v_unused_1052_);
v___x_1045_ = v___x_1043_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v___x_1043_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(0);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1043_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1043_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(v_x_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v_x_1064_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object* v_o_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1083_, v___y_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object* v_o_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(v_o_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object* v___x_1093_, uint8_t v___x_1094_, lean_object* v___x_1095_, lean_object* v_as_1096_, lean_object* v_as_x27_1097_, lean_object* v_b_1098_, lean_object* v_a_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_1093_, v___x_1094_, v___x_1095_, v_as_x27_1097_, v_b_1098_, v___y_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v_as_1107_, lean_object* v_as_x27_1108_, lean_object* v_b_1109_, lean_object* v_a_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v___x_10507__boxed_1114_; lean_object* v_res_1115_; 
v___x_10507__boxed_1114_ = lean_unbox(v___x_1105_);
v_res_1115_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(v___x_1104_, v___x_10507__boxed_1114_, v___x_1106_, v_as_1107_, v_as_x27_1108_, v_b_1109_, v_a_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v_as_x27_1108_);
lean_dec(v_as_1107_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_msgData_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_1116_, v___y_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(v_msgData_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModuleLinter));
v___x_1128_ = l_Lean_Elab_Command_addLinter(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
return v_res_1130_;
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
