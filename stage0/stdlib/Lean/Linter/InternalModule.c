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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(lean_object* v___y_206_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg___boxed(lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_212_);
lean_dec(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___boxed(lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1(v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(lean_object* v_opts_223_, lean_object* v_opt_224_){
_start:
{
lean_object* v_name_225_; lean_object* v_defValue_226_; lean_object* v_map_227_; lean_object* v___x_228_; 
v_name_225_ = lean_ctor_get(v_opt_224_, 0);
v_defValue_226_ = lean_ctor_get(v_opt_224_, 1);
v_map_227_ = lean_ctor_get(v_opts_223_, 0);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_227_, v_name_225_);
if (lean_obj_tag(v___x_228_) == 0)
{
uint8_t v___x_229_; 
v___x_229_ = lean_unbox(v_defValue_226_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
if (lean_obj_tag(v_val_230_) == 1)
{
uint8_t v_v_231_; 
v_v_231_ = lean_ctor_get_uint8(v_val_230_, 0);
lean_dec_ref_known(v_val_230_, 0);
return v_v_231_;
}
else
{
uint8_t v___x_232_; 
lean_dec(v_val_230_);
v___x_232_ = lean_unbox(v_defValue_226_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8___boxed(lean_object* v_opts_233_, lean_object* v_opt_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_233_, v_opt_234_);
lean_dec_ref(v_opt_234_);
lean_dec_ref(v_opts_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(uint8_t v_suppressElabErrors_238_, uint8_t v___y_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 1)
{
lean_object* v_pre_241_; 
v_pre_241_ = lean_ctor_get(v_x_240_, 0);
if (lean_obj_tag(v_pre_241_) == 0)
{
lean_object* v_str_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_str_242_ = lean_ctor_get(v_x_240_, 1);
v___x_243_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___closed__0));
v___x_244_ = lean_string_dec_eq(v_str_242_, v___x_243_);
if (v___x_244_ == 0)
{
return v___x_244_;
}
else
{
return v_suppressElabErrors_238_;
}
}
else
{
return v___y_239_;
}
}
else
{
return v___y_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_245_, lean_object* v___y_246_, lean_object* v_x_247_){
_start:
{
uint8_t v_suppressElabErrors_boxed_248_; uint8_t v___y_7885__boxed_249_; uint8_t v_res_250_; lean_object* v_r_251_; 
v_suppressElabErrors_boxed_248_ = lean_unbox(v_suppressElabErrors_245_);
v___y_7885__boxed_249_ = lean_unbox(v___y_246_);
v_res_250_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(v_suppressElabErrors_boxed_248_, v___y_7885__boxed_249_, v_x_247_);
lean_dec(v_x_247_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_252_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_ctor_set(v___x_257_, 3, v___x_256_);
lean_ctor_set(v___x_257_, 4, v___x_255_);
lean_ctor_set(v___x_257_, 5, v___x_255_);
lean_ctor_set(v___x_257_, 6, v___x_255_);
lean_ctor_set(v___x_257_, 7, v___x_255_);
lean_ctor_set(v___x_257_, 8, v___x_255_);
lean_ctor_set(v___x_257_, 9, v___x_255_);
lean_ctor_set(v___x_257_, 10, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(32u);
v___x_259_ = lean_mk_empty_array_with_capacity(v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_261_ = ((size_t)5ULL);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_unsigned_to_nat(32u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__3);
v___x_266_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
lean_ctor_set(v___x_266_, 2, v___x_262_);
lean_ctor_set(v___x_266_, 3, v___x_262_);
lean_ctor_set_usize(v___x_266_, 4, v___x_261_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_box(1);
v___x_268_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__4);
v___x_269_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
lean_ctor_set(v___x_270_, 2, v___x_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_msgData_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_env_275_; lean_object* v___x_276_; lean_object* v_scopes_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_opts_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_274_ = lean_st_ref_get(v___y_272_);
v_env_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_env_275_);
lean_dec(v___x_274_);
v___x_276_ = lean_st_ref_get(v___y_272_);
v_scopes_277_ = lean_ctor_get(v___x_276_, 2);
lean_inc(v_scopes_277_);
lean_dec(v___x_276_);
v___x_278_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_279_ = l_List_head_x21___redArg(v___x_278_, v_scopes_277_);
lean_dec(v_scopes_277_);
v_opts_280_ = lean_ctor_get(v___x_279_, 1);
lean_inc_ref(v_opts_280_);
lean_dec(v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__2);
v___x_282_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___closed__5);
v___x_283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_283_, 0, v_env_275_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
lean_ctor_set(v___x_283_, 3, v_opts_280_);
v___x_284_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_msgData_271_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_286_, v___y_287_);
lean_dec(v___y_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(lean_object* v_ref_291_, lean_object* v_msgData_292_, uint8_t v_severity_293_, uint8_t v_isSilent_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; uint8_t v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; uint8_t v___y_366_; lean_object* v___y_367_; uint8_t v___y_391_; uint8_t v___y_392_; lean_object* v___y_393_; uint8_t v___y_394_; lean_object* v___y_395_; uint8_t v___y_399_; uint8_t v___y_400_; uint8_t v___y_401_; uint8_t v___x_416_; uint8_t v___y_418_; uint8_t v___y_419_; uint8_t v___y_420_; uint8_t v___y_422_; uint8_t v___x_434_; 
v___x_416_ = 2;
v___x_434_ = l_Lean_instBEqMessageSeverity_beq(v_severity_293_, v___x_416_);
if (v___x_434_ == 0)
{
v___y_422_ = v___x_434_;
goto v___jp_421_;
}
else
{
uint8_t v___x_435_; 
lean_inc_ref(v_msgData_292_);
v___x_435_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_292_);
v___y_422_ = v___x_435_;
goto v___jp_421_;
}
v___jp_298_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Elab_Command_getScope___redArg(v___y_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = l_Lean_Elab_Command_getScope___redArg(v___y_306_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_345_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_345_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_345_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_345_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v_currNamespace_315_; lean_object* v_openDecls_316_; lean_object* v_env_317_; lean_object* v_messages_318_; lean_object* v_scopes_319_; lean_object* v_usedQuotCtxts_320_; lean_object* v_nextMacroScope_321_; lean_object* v_maxRecDepth_322_; lean_object* v_ngen_323_; lean_object* v_auxDeclNGen_324_; lean_object* v_infoState_325_; lean_object* v_traceState_326_; lean_object* v_snapshotTasks_327_; lean_object* v_prevLinterStates_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_344_; 
v___x_314_ = lean_st_ref_take(v___y_306_);
v_currNamespace_315_ = lean_ctor_get(v_a_308_, 2);
lean_inc(v_currNamespace_315_);
lean_dec(v_a_308_);
v_openDecls_316_ = lean_ctor_get(v_a_310_, 3);
lean_inc(v_openDecls_316_);
lean_dec(v_a_310_);
v_env_317_ = lean_ctor_get(v___x_314_, 0);
v_messages_318_ = lean_ctor_get(v___x_314_, 1);
v_scopes_319_ = lean_ctor_get(v___x_314_, 2);
v_usedQuotCtxts_320_ = lean_ctor_get(v___x_314_, 3);
v_nextMacroScope_321_ = lean_ctor_get(v___x_314_, 4);
v_maxRecDepth_322_ = lean_ctor_get(v___x_314_, 5);
v_ngen_323_ = lean_ctor_get(v___x_314_, 6);
v_auxDeclNGen_324_ = lean_ctor_get(v___x_314_, 7);
v_infoState_325_ = lean_ctor_get(v___x_314_, 8);
v_traceState_326_ = lean_ctor_get(v___x_314_, 9);
v_snapshotTasks_327_ = lean_ctor_get(v___x_314_, 10);
v_prevLinterStates_328_ = lean_ctor_get(v___x_314_, 11);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_344_ == 0)
{
v___x_330_ = v___x_314_;
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_prevLinterStates_328_);
lean_inc(v_snapshotTasks_327_);
lean_inc(v_traceState_326_);
lean_inc(v_infoState_325_);
lean_inc(v_auxDeclNGen_324_);
lean_inc(v_ngen_323_);
lean_inc(v_maxRecDepth_322_);
lean_inc(v_nextMacroScope_321_);
lean_inc(v_usedQuotCtxts_320_);
lean_inc(v_scopes_319_);
lean_inc(v_messages_318_);
lean_inc(v_env_317_);
lean_dec(v___x_314_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_currNamespace_315_);
lean_ctor_set(v___x_332_, 1, v_openDecls_316_);
v___x_333_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___y_305_);
lean_inc_ref(v___y_299_);
lean_inc_ref(v___y_304_);
v___x_334_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_334_, 0, v___y_304_);
lean_ctor_set(v___x_334_, 1, v___y_302_);
lean_ctor_set(v___x_334_, 2, v___y_300_);
lean_ctor_set(v___x_334_, 3, v___y_299_);
lean_ctor_set(v___x_334_, 4, v___x_333_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5, v___y_303_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5 + 1, v___y_301_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5 + 2, v_isSilent_294_);
v___x_335_ = l_Lean_MessageLog_add(v___x_334_, v_messages_318_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_335_);
v___x_337_ = v___x_330_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_env_317_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_scopes_319_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_usedQuotCtxts_320_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_nextMacroScope_321_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v_maxRecDepth_322_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_ngen_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 7, v_auxDeclNGen_324_);
lean_ctor_set(v_reuseFailAlloc_343_, 8, v_infoState_325_);
lean_ctor_set(v_reuseFailAlloc_343_, 9, v_traceState_326_);
lean_ctor_set(v_reuseFailAlloc_343_, 10, v_snapshotTasks_327_);
lean_ctor_set(v_reuseFailAlloc_343_, 11, v_prevLinterStates_328_);
v___x_337_ = v_reuseFailAlloc_343_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = lean_st_ref_put(v___y_306_, v___x_337_);
v___x_339_ = lean_box(0);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_339_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_308_);
lean_dec_ref(v___y_305_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_300_);
v_a_346_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_309_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_309_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v___y_305_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_300_);
v_a_354_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_307_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_307_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
v___jp_362_:
{
lean_object* v_fileName_368_; lean_object* v_fileMap_369_; uint8_t v_suppressElabErrors_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_389_; 
v_fileName_368_ = lean_ctor_get(v___y_295_, 0);
v_fileMap_369_ = lean_ctor_get(v___y_295_, 1);
v_suppressElabErrors_370_ = lean_ctor_get_uint8(v___y_295_, sizeof(void*)*10);
v___x_371_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_292_);
v___x_372_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v___x_371_, v___y_296_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_389_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_389_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_389_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc_ref_n(v_fileMap_369_, 2);
v___x_377_ = l_Lean_FileMap_toPosition(v_fileMap_369_, v___y_364_);
lean_dec(v___y_364_);
v___x_378_ = l_Lean_FileMap_toPosition(v_fileMap_369_, v___y_367_);
lean_dec(v___y_367_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0));
if (v_suppressElabErrors_370_ == 0)
{
lean_del_object(v___x_375_);
v___y_299_ = v___x_380_;
v___y_300_ = v___x_379_;
v___y_301_ = v___y_365_;
v___y_302_ = v___x_377_;
v___y_303_ = v___y_366_;
v___y_304_ = v_fileName_368_;
v___y_305_ = v_a_373_;
v___y_306_ = v___y_296_;
goto v___jp_298_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___f_383_; uint8_t v___x_384_; 
v___x_381_ = lean_box(v_suppressElabErrors_370_);
v___x_382_ = lean_box(v___y_363_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_383_, 0, v___x_381_);
lean_closure_set(v___f_383_, 1, v___x_382_);
lean_inc(v_a_373_);
v___x_384_ = l_Lean_MessageData_hasTag(v___f_383_, v_a_373_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_dec_ref_known(v___x_379_, 1);
lean_dec_ref(v___x_377_);
lean_dec(v_a_373_);
v___x_385_ = lean_box(0);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_385_);
v___x_387_ = v___x_375_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_del_object(v___x_375_);
v___y_299_ = v___x_380_;
v___y_300_ = v___x_379_;
v___y_301_ = v___y_365_;
v___y_302_ = v___x_377_;
v___y_303_ = v___y_366_;
v___y_304_ = v_fileName_368_;
v___y_305_ = v_a_373_;
v___y_306_ = v___y_296_;
goto v___jp_298_;
}
}
}
}
v___jp_390_:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Syntax_getTailPos_x3f(v___y_393_, v___y_394_);
lean_dec(v___y_393_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_inc(v___y_395_);
v___y_363_ = v___y_391_;
v___y_364_ = v___y_395_;
v___y_365_ = v___y_392_;
v___y_366_ = v___y_394_;
v___y_367_ = v___y_395_;
goto v___jp_362_;
}
else
{
lean_object* v_val_397_; 
v_val_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_396_, 1);
v___y_363_ = v___y_391_;
v___y_364_ = v___y_395_;
v___y_365_ = v___y_392_;
v___y_366_ = v___y_394_;
v___y_367_ = v_val_397_;
goto v___jp_362_;
}
}
v___jp_398_:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_Command_getRef___redArg(v___y_295_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_ref_404_; lean_object* v___x_405_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v_ref_404_ = l_Lean_replaceRef(v_ref_291_, v_a_403_);
lean_dec(v_a_403_);
v___x_405_ = l_Lean_Syntax_getPos_x3f(v_ref_404_, v___y_400_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___y_391_ = v___y_399_;
v___y_392_ = v___y_401_;
v___y_393_ = v_ref_404_;
v___y_394_ = v___y_400_;
v___y_395_ = v___x_406_;
goto v___jp_390_;
}
else
{
lean_object* v_val_407_; 
v_val_407_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_405_, 1);
v___y_391_ = v___y_399_;
v___y_392_ = v___y_401_;
v___y_393_ = v_ref_404_;
v___y_394_ = v___y_400_;
v___y_395_ = v_val_407_;
goto v___jp_390_;
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_msgData_292_);
v_a_408_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_402_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_402_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
v___jp_417_:
{
if (v___y_420_ == 0)
{
v___y_399_ = v___y_418_;
v___y_400_ = v___y_419_;
v___y_401_ = v_severity_293_;
goto v___jp_398_;
}
else
{
v___y_399_ = v___y_418_;
v___y_400_ = v___y_419_;
v___y_401_ = v___x_416_;
goto v___jp_398_;
}
}
v___jp_421_:
{
if (v___y_422_ == 0)
{
lean_object* v___x_423_; lean_object* v_scopes_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_opts_427_; uint8_t v___x_428_; uint8_t v___x_429_; 
v___x_423_ = lean_st_ref_get(v___y_296_);
v_scopes_424_ = lean_ctor_get(v___x_423_, 2);
lean_inc(v_scopes_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_426_ = l_List_head_x21___redArg(v___x_425_, v_scopes_424_);
lean_dec(v_scopes_424_);
v_opts_427_ = lean_ctor_get(v___x_426_, 1);
lean_inc_ref(v_opts_427_);
lean_dec(v___x_426_);
v___x_428_ = 1;
v___x_429_ = l_Lean_instBEqMessageSeverity_beq(v_severity_293_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec_ref(v_opts_427_);
v___y_418_ = v___y_422_;
v___y_419_ = v___y_422_;
v___y_420_ = v___x_429_;
goto v___jp_417_;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = l_Lean_warningAsError;
v___x_431_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_427_, v___x_430_);
lean_dec_ref(v_opts_427_);
v___y_418_ = v___y_422_;
v___y_419_ = v___y_422_;
v___y_420_ = v___x_431_;
goto v___jp_417_;
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_msgData_292_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_436_, lean_object* v_msgData_437_, lean_object* v_severity_438_, lean_object* v_isSilent_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v_severity_boxed_443_; uint8_t v_isSilent_boxed_444_; lean_object* v_res_445_; 
v_severity_boxed_443_ = lean_unbox(v_severity_438_);
v_isSilent_boxed_444_ = lean_unbox(v_isSilent_439_);
v_res_445_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_436_, v_msgData_437_, v_severity_boxed_443_, v_isSilent_boxed_444_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v_ref_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(lean_object* v_ref_446_, lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; 
v___x_451_ = 1;
v___x_452_ = 0;
v___x_453_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_446_, v_msgData_447_, v___x_451_, v___x_452_, v___y_448_, v___y_449_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3___boxed(lean_object* v_ref_454_, lean_object* v_msgData_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_ref_454_, v_msgData_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_ref_454_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object* v_linterOption_466_, lean_object* v_stx_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_name_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_490_; 
v_name_472_ = lean_ctor_get(v_linterOption_466_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_linterOption_466_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_linterOption_466_, 1);
lean_dec(v_unused_491_);
v___x_474_ = v_linterOption_466_;
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_name_472_);
lean_dec(v_linterOption_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_490_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1);
lean_inc(v_name_472_);
v___x_477_ = l_Lean_MessageData_ofName(v_name_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 7);
lean_ctor_set(v___x_474_, 1, v___x_477_);
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_489_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_disable_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_480_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v_disable_482_ = l_Lean_MessageData_note(v___x_481_);
v___x_483_ = l_Lean_Linter_linterMessageTag;
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v_msg_468_);
lean_ctor_set(v___x_484_, 1, v_disable_482_);
v___x_485_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_486_, 0, v_name_472_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_inc(v_stx_467_);
v___x_487_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_487_, 0, v_stx_467_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_stx_467_, v___x_487_, v___y_469_, v___y_470_);
lean_dec(v_stx_467_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object* v_linterOption_492_, lean_object* v_stx_493_, lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v_linterOption_492_, v_stx_493_, v_msg_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_498_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object* v___x_508_, uint8_t v___x_509_, lean_object* v___x_510_, lean_object* v_as_x27_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
if (lean_obj_tag(v_as_x27_511_) == 0)
{
lean_object* v___x_516_; 
lean_dec(v___x_510_);
lean_dec_ref(v___x_508_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_512_);
return v___x_516_;
}
else
{
lean_object* v_head_517_; lean_object* v_tail_518_; uint8_t v___x_519_; 
v_head_517_ = lean_ctor_get(v_as_x27_511_, 0);
v_tail_518_ = lean_ctor_get(v_as_x27_511_, 1);
v___x_519_ = l_Lean_NameSet_contains(v_b_512_, v_head_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
lean_inc_n(v_head_517_, 2);
v___x_520_ = l_Lean_NameSet_insert(v_b_512_, v_head_517_);
lean_inc_ref(v___x_508_);
v___x_521_ = l_Lean_Environment_contains(v___x_508_, v_head_517_, v___x_509_);
if (v___x_521_ == 0)
{
v_as_x27_511_ = v_tail_518_;
v_b_512_ = v___x_520_;
goto _start;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_Linter_InternalModule_isInternalDecl(v_head_517_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Elab_Command_getRef___redArg(v___y_513_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_527_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1);
lean_inc(v_head_517_);
v___x_528_ = l_Lean_MessageData_ofConstName(v_head_517_, v___x_523_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_inc(v___x_510_);
v___x_532_ = l_Lean_MessageData_ofName(v___x_510_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v___x_526_, v_a_525_, v___x_535_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_dec_ref_known(v___x_536_, 1);
v_as_x27_511_ = v_tail_518_;
v_b_512_ = v___x_520_;
goto _start;
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v___x_520_);
lean_dec(v___x_510_);
lean_dec_ref(v___x_508_);
v_a_538_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_536_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v___x_520_);
lean_dec(v___x_510_);
lean_dec_ref(v___x_508_);
v_a_546_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_524_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_524_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
v_as_x27_511_ = v_tail_518_;
v_b_512_ = v___x_520_;
goto _start;
}
}
}
else
{
v_as_x27_511_ = v_tail_518_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v_as_x27_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_8351__boxed_564_; lean_object* v_res_565_; 
v___x_8351__boxed_564_ = lean_unbox(v___x_557_);
v_res_565_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_556_, v___x_8351__boxed_564_, v___x_558_, v_as_x27_559_, v_b_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v_as_x27_559_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object* v___x_566_, uint8_t v___x_567_, lean_object* v___x_568_, lean_object* v_as_569_, size_t v_sz_570_, size_t v_i_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_571_, v_sz_570_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v___x_568_);
lean_dec_ref(v___x_566_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_b_572_);
return v___x_577_;
}
else
{
lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_snd_578_ = lean_ctor_get(v_b_572_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_b_572_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_b_572_, 0);
lean_dec(v_unused_602_);
v___x_580_ = v_b_572_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_dec(v_b_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_582_ = lean_array_uget_borrowed(v_as_569_, v_i_571_);
lean_inc(v_a_582_);
v___x_583_ = l_Lean_Linter_getNewDecls(v_a_582_);
lean_inc(v___x_568_);
lean_inc_ref(v___x_566_);
v___x_584_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_566_, v___x_567_, v___x_568_, v___x_583_, v_snd_578_, v___y_573_, v___y_574_);
lean_dec(v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_box(0);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_a_585_);
lean_ctor_set(v___x_580_, 0, v___x_586_);
v___x_588_ = v___x_580_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_585_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
size_t v___x_589_; size_t v___x_590_; 
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_571_, v___x_589_);
v_i_571_ = v___x_590_;
v_b_572_ = v___x_588_;
goto _start;
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_del_object(v___x_580_);
lean_dec(v___x_568_);
lean_dec_ref(v___x_566_);
v_a_593_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_584_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_584_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v_as_606_, lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
uint8_t v___x_8459__boxed_613_; size_t v_sz_boxed_614_; size_t v_i_boxed_615_; lean_object* v_res_616_; 
v___x_8459__boxed_613_ = lean_unbox(v___x_604_);
v_sz_boxed_614_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_615_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_603_, v___x_8459__boxed_613_, v___x_605_, v_as_606_, v_sz_boxed_614_, v_i_boxed_615_, v_b_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec_ref(v_as_606_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object* v___x_617_, uint8_t v___x_618_, lean_object* v___x_619_, lean_object* v_as_620_, size_t v_sz_621_, size_t v_i_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_usize_dec_lt(v_i_622_, v_sz_621_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec(v___x_619_);
lean_dec_ref(v___x_617_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_623_);
return v___x_628_;
}
else
{
lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_652_; 
v_snd_629_ = lean_ctor_get(v_b_623_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_b_623_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v_b_623_, 0);
lean_dec(v_unused_653_);
v___x_631_ = v_b_623_;
v_isShared_632_ = v_isSharedCheck_652_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_dec(v_b_623_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_652_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_633_ = lean_array_uget_borrowed(v_as_620_, v_i_622_);
lean_inc(v_a_633_);
v___x_634_ = l_Lean_Linter_getNewDecls(v_a_633_);
lean_inc(v___x_619_);
lean_inc_ref(v___x_617_);
v___x_635_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_617_, v___x_618_, v___x_619_, v___x_634_, v_snd_629_, v___y_624_, v___y_625_);
lean_dec(v___x_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = lean_box(0);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_a_636_);
lean_ctor_set(v___x_631_, 0, v___x_637_);
v___x_639_ = v___x_631_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_a_636_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_622_, v___x_640_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_617_, v___x_618_, v___x_619_, v_as_620_, v_sz_621_, v___x_641_, v___x_639_, v___y_624_, v___y_625_);
return v___x_642_;
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_631_);
lean_dec(v___x_619_);
lean_dec_ref(v___x_617_);
v_a_644_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_635_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v_as_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_b_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
uint8_t v___x_8527__boxed_664_; size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v___x_8527__boxed_664_ = lean_unbox(v___x_655_);
v_sz_boxed_665_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_666_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_654_, v___x_8527__boxed_664_, v___x_656_, v_as_657_, v_sz_boxed_665_, v_i_boxed_666_, v_b_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec_ref(v_as_657_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object* v___x_668_, uint8_t v___x_669_, lean_object* v___x_670_, lean_object* v_as_671_, size_t v_sz_672_, size_t v_i_673_, lean_object* v_b_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_673_, v_sz_672_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec(v___x_670_);
lean_dec_ref(v___x_668_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_b_674_);
return v___x_679_;
}
else
{
lean_object* v_snd_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_703_; 
v_snd_680_ = lean_ctor_get(v_b_674_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_674_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_b_674_, 0);
lean_dec(v_unused_704_);
v___x_682_ = v_b_674_;
v_isShared_683_ = v_isSharedCheck_703_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snd_680_);
lean_dec(v_b_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_703_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_a_684_ = lean_array_uget_borrowed(v_as_671_, v_i_673_);
lean_inc(v_a_684_);
v___x_685_ = l_Lean_Linter_getNewDecls(v_a_684_);
lean_inc(v___x_670_);
lean_inc_ref(v___x_668_);
v___x_686_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_668_, v___x_669_, v___x_670_, v___x_685_, v_snd_680_, v___y_675_, v___y_676_);
lean_dec(v___x_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_box(0);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_a_687_);
lean_ctor_set(v___x_682_, 0, v___x_688_);
v___x_690_ = v___x_682_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_687_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_673_, v___x_691_);
v_i_673_ = v___x_692_;
v_b_674_ = v___x_690_;
goto _start;
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_del_object(v___x_682_);
lean_dec(v___x_670_);
lean_dec_ref(v___x_668_);
v_a_695_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_686_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_686_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_as_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_8595__boxed_715_; size_t v_sz_boxed_716_; size_t v_i_boxed_717_; lean_object* v_res_718_; 
v___x_8595__boxed_715_ = lean_unbox(v___x_706_);
v_sz_boxed_716_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_717_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_705_, v___x_8595__boxed_715_, v___x_707_, v_as_708_, v_sz_boxed_716_, v_i_boxed_717_, v_b_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_as_708_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object* v___x_719_, uint8_t v___x_720_, lean_object* v___x_721_, lean_object* v_as_722_, size_t v_sz_723_, size_t v_i_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_lt(v_i_724_, v_sz_723_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v___x_721_);
lean_dec_ref(v___x_719_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_725_);
return v___x_730_;
}
else
{
lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_754_; 
v_snd_731_ = lean_ctor_get(v_b_725_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_b_725_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_b_725_, 0);
lean_dec(v_unused_755_);
v___x_733_ = v_b_725_;
v_isShared_734_ = v_isSharedCheck_754_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_dec(v_b_725_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_754_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_a_735_ = lean_array_uget_borrowed(v_as_722_, v_i_724_);
lean_inc(v_a_735_);
v___x_736_ = l_Lean_Linter_getNewDecls(v_a_735_);
lean_inc(v___x_721_);
lean_inc_ref(v___x_719_);
v___x_737_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_719_, v___x_720_, v___x_721_, v___x_736_, v_snd_731_, v___y_726_, v___y_727_);
lean_dec(v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_box(0);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_738_);
lean_ctor_set(v___x_733_, 0, v___x_739_);
v___x_741_ = v___x_733_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_738_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_724_, v___x_742_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_719_, v___x_720_, v___x_721_, v_as_722_, v_sz_723_, v___x_743_, v___x_741_, v___y_726_, v___y_727_);
return v___x_744_;
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_del_object(v___x_733_);
lean_dec(v___x_721_);
lean_dec_ref(v___x_719_);
v_a_746_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_737_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_756_, lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v_as_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
uint8_t v___x_8663__boxed_766_; size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v___x_8663__boxed_766_ = lean_unbox(v___x_757_);
v_sz_boxed_767_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_768_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_756_, v___x_8663__boxed_766_, v___x_758_, v_as_759_, v_sz_boxed_767_, v_i_boxed_768_, v_b_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_as_759_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object* v_init_770_, lean_object* v___x_771_, uint8_t v___x_772_, lean_object* v___x_773_, lean_object* v_n_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
if (lean_obj_tag(v_n_774_) == 0)
{
lean_object* v_cs_779_; lean_object* v___x_780_; lean_object* v___x_781_; size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; 
v_cs_779_ = lean_ctor_get(v_n_774_, 0);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_b_775_);
v_sz_782_ = lean_array_size(v_cs_779_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_770_, v___x_771_, v___x_772_, v___x_773_, v_cs_779_, v_sz_782_, v___x_783_, v___x_781_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_799_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_799_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_799_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_799_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fst_789_; 
v_fst_789_ = lean_ctor_get(v_a_785_, 0);
if (lean_obj_tag(v_fst_789_) == 0)
{
lean_object* v_snd_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v_snd_790_ = lean_ctor_get(v_a_785_, 1);
lean_inc(v_snd_790_);
lean_dec(v_a_785_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_snd_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_791_);
v___x_793_ = v___x_787_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_object* v_val_795_; lean_object* v___x_797_; 
lean_inc_ref(v_fst_789_);
lean_dec(v_a_785_);
v_val_795_ = lean_ctor_get(v_fst_789_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_fst_789_, 1);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_val_795_);
v___x_797_ = v___x_787_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_val_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
v_a_800_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_784_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_784_);
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
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_vs_808_; lean_object* v___x_809_; lean_object* v___x_810_; size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; 
v_vs_808_ = lean_ctor_get(v_n_774_, 0);
v___x_809_ = lean_box(0);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_b_775_);
v_sz_811_ = lean_array_size(v_vs_808_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_771_, v___x_772_, v___x_773_, v_vs_808_, v_sz_811_, v___x_812_, v___x_810_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_828_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_fst_818_; 
v_fst_818_ = lean_ctor_get(v_a_814_, 0);
if (lean_obj_tag(v_fst_818_) == 0)
{
lean_object* v_snd_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v_snd_819_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_snd_819_);
lean_dec(v_a_814_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_snd_819_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
lean_inc_ref(v_fst_818_);
lean_dec(v_a_814_);
v_val_824_ = lean_ctor_get(v_fst_818_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v_fst_818_, 1);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_val_824_);
v___x_826_ = v___x_816_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_813_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_813_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object* v_init_837_, lean_object* v___x_838_, uint8_t v___x_839_, lean_object* v___x_840_, lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_dec(v___x_840_);
lean_dec_ref(v___x_838_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v_b_844_);
return v___x_849_;
}
else
{
lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_884_; 
v_snd_850_ = lean_ctor_get(v_b_844_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_b_844_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_b_844_, 0);
lean_dec(v_unused_885_);
v___x_852_ = v_b_844_;
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_dec(v_b_844_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_884_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
lean_inc(v_snd_850_);
lean_inc(v___x_840_);
lean_inc_ref(v___x_838_);
v___x_855_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_837_, v___x_838_, v___x_839_, v___x_840_, v_a_854_, v_snd_850_, v___y_845_, v___y_846_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_875_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_875_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
if (lean_obj_tag(v_a_856_) == 0)
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v___x_840_);
lean_dec_ref(v___x_838_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_a_856_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_860_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_snd_850_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_862_);
v___x_864_ = v___x_858_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_del_object(v___x_858_);
lean_dec(v_snd_850_);
v_a_867_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v_a_856_, 1);
v___x_868_ = lean_box(0);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_a_867_);
lean_ctor_set(v___x_852_, 0, v___x_868_);
v___x_870_ = v___x_852_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_867_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
size_t v___x_871_; size_t v___x_872_; 
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_843_, v___x_871_);
v_i_843_ = v___x_872_;
v_b_844_ = v___x_870_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v___x_840_);
lean_dec_ref(v___x_838_);
v_a_876_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_855_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_855_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_as_890_, lean_object* v_sz_891_, lean_object* v_i_892_, lean_object* v_b_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v___x_8731__boxed_897_; size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v___x_8731__boxed_897_ = lean_unbox(v___x_888_);
v_sz_boxed_898_ = lean_unbox_usize(v_sz_891_);
lean_dec(v_sz_891_);
v_i_boxed_899_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_886_, v___x_887_, v___x_8731__boxed_897_, v___x_889_, v_as_890_, v_sz_boxed_898_, v_i_boxed_899_, v_b_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_as_890_);
lean_dec(v_init_886_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object* v_init_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_n_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v___x_8753__boxed_910_; lean_object* v_res_911_; 
v___x_8753__boxed_910_ = lean_unbox(v___x_903_);
v_res_911_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_901_, v___x_902_, v___x_8753__boxed_910_, v___x_904_, v_n_905_, v_b_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_n_905_);
lean_dec(v_init_901_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object* v___x_912_, uint8_t v___x_913_, lean_object* v___x_914_, lean_object* v_t_915_, lean_object* v_init_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_root_920_; lean_object* v_tail_921_; lean_object* v___x_922_; 
v_root_920_ = lean_ctor_get(v_t_915_, 0);
v_tail_921_ = lean_ctor_get(v_t_915_, 1);
lean_inc(v___x_914_);
lean_inc_ref(v___x_912_);
lean_inc(v_init_916_);
v___x_922_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_916_, v___x_912_, v___x_913_, v___x_914_, v_root_920_, v_init_916_, v___y_917_, v___y_918_);
lean_dec(v_init_916_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_959_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_959_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_959_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_959_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; 
lean_dec(v___x_914_);
lean_dec_ref(v___x_912_);
v_a_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v_a_923_, 1);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_a_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_932_; lean_object* v___x_933_; size_t v_sz_934_; size_t v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_925_);
v_a_931_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v_a_923_, 1);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_931_);
v_sz_934_ = lean_array_size(v_tail_921_);
v___x_935_ = ((size_t)0ULL);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_912_, v___x_913_, v___x_914_, v_tail_921_, v_sz_934_, v___x_935_, v___x_933_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_950_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_fst_941_; 
v_fst_941_ = lean_ctor_get(v_a_937_, 0);
if (lean_obj_tag(v_fst_941_) == 0)
{
lean_object* v_snd_942_; lean_object* v___x_944_; 
v_snd_942_ = lean_ctor_get(v_a_937_, 1);
lean_inc(v_snd_942_);
lean_dec(v_a_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_snd_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_snd_942_);
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
lean_object* v_val_946_; lean_object* v___x_948_; 
lean_inc_ref(v_fst_941_);
lean_dec(v_a_937_);
v_val_946_ = lean_ctor_get(v_fst_941_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_fst_941_, 1);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_val_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_946_);
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
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_936_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_936_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v___x_914_);
lean_dec_ref(v___x_912_);
v_a_960_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_922_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_922_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v_t_971_, lean_object* v_init_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v___x_8944__boxed_976_; lean_object* v_res_977_; 
v___x_8944__boxed_976_ = lean_unbox(v___x_969_);
v_res_977_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v___x_968_, v___x_8944__boxed_976_, v___x_970_, v_t_971_, v_init_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_t_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object* v_o_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v_env_982_; lean_object* v___x_983_; lean_object* v_toEnvExtension_984_; lean_object* v_asyncMode_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_merged_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v___x_981_ = lean_st_ref_get(v___y_979_);
v_env_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_env_982_);
lean_dec(v___x_981_);
v___x_983_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_984_ = lean_ctor_get(v___x_983_, 0);
v_asyncMode_985_ = lean_ctor_get(v_toEnvExtension_984_, 2);
v___x_986_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_987_ = lean_box(0);
v___x_988_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_986_, v___x_983_, v_env_982_, v_asyncMode_985_, v___x_987_);
v_merged_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_988_, 1);
lean_dec(v_unused_998_);
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_merged_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_merged_989_);
lean_ctor_set(v___x_991_, 0, v_o_978_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_o_978_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_merged_989_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_999_, v___y_1000_);
lean_dec(v___y_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v_scopes_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_opts_1010_; lean_object* v___x_1011_; 
v___x_1006_ = lean_st_ref_get(v___y_1004_);
v_scopes_1007_ = lean_ctor_get(v___x_1006_, 2);
lean_inc(v_scopes_1007_);
lean_dec(v___x_1006_);
v___x_1008_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1009_ = l_List_head_x21___redArg(v___x_1008_, v_scopes_1007_);
lean_dec(v_scopes_1007_);
v_opts_1010_ = lean_ctor_get(v___x_1009_, 1);
lean_inc_ref(v_opts_1010_);
lean_dec(v___x_1009_);
v___x_1011_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_opts_1010_, v___y_1004_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object* v_x_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_messages_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_st_ref_get(v___y_1018_);
v_messages_1021_ = lean_ctor_get(v___x_1020_, 1);
lean_inc_ref(v_messages_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = l_Lean_MessageLog_hasErrors(v_messages_1021_);
lean_dec_ref(v_messages_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1063_; 
v___x_1023_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1017_, v___y_1018_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1063_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1063_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_1029_ = l_Lean_Linter_getLinterValue(v___x_1028_, v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1030_);
v___x_1032_ = v___x_1026_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v_env_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1034_ = lean_st_ref_get(v___y_1018_);
v_env_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1035_);
lean_dec(v___x_1034_);
v___x_1036_ = l_Lean_Environment_mainModule(v_env_1035_);
v___x_1037_ = l_Lean_Linter_InternalModule_isInternalModule(v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_dec(v___x_1036_);
lean_dec_ref(v_env_1035_);
v___x_1038_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1038_);
v___x_1040_ = v___x_1026_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1026_);
v___x_1042_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_1018_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = l_Lean_NameSet_empty;
v___x_1045_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v_env_1035_, v___x_1037_, v___x_1036_, v_a_1043_, v___x_1044_, v___y_1017_, v___y_1018_);
lean_dec(v_a_1043_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1045_, 0);
lean_dec(v_unused_1054_);
v___x_1047_ = v___x_1045_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_dec(v___x_1045_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1045_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object* v_x_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(v_x_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v_x_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object* v_o_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1085_, v___y_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object* v_o_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(v_o_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object* v___x_1095_, uint8_t v___x_1096_, lean_object* v___x_1097_, lean_object* v_as_1098_, lean_object* v_as_x27_1099_, lean_object* v_b_1100_, lean_object* v_a_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_1095_, v___x_1096_, v___x_1097_, v_as_x27_1099_, v_b_1100_, v___y_1102_, v___y_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v_as_1109_, lean_object* v_as_x27_1110_, lean_object* v_b_1111_, lean_object* v_a_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_9256__boxed_1116_; lean_object* v_res_1117_; 
v___x_9256__boxed_1116_ = lean_unbox(v___x_1107_);
v_res_1117_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(v___x_1106_, v___x_9256__boxed_1116_, v___x_1108_, v_as_1109_, v_as_x27_1110_, v_b_1111_, v_a_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v_as_x27_1110_);
lean_dec(v_as_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_1118_, v___y_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_msgData_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(v_msgData_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModuleLinter));
v___x_1130_ = l_Lean_Elab_Command_addLinter(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
return v_res_1132_;
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
