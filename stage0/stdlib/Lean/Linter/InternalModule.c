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
uint8_t v_suppressElabErrors_boxed_248_; uint8_t v___y_7905__boxed_249_; uint8_t v_res_250_; lean_object* v_r_251_; 
v_suppressElabErrors_boxed_248_ = lean_unbox(v_suppressElabErrors_245_);
v___y_7905__boxed_249_ = lean_unbox(v___y_246_);
v_res_250_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0(v_suppressElabErrors_boxed_248_, v___y_7905__boxed_249_, v_x_247_);
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
lean_object* v___y_299_; lean_object* v___y_300_; uint8_t v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; uint8_t v___y_305_; lean_object* v___y_306_; uint8_t v___y_364_; lean_object* v___y_365_; uint8_t v___y_366_; uint8_t v___y_367_; lean_object* v___y_368_; uint8_t v___y_392_; lean_object* v___y_393_; uint8_t v___y_394_; uint8_t v___y_395_; lean_object* v___y_396_; uint8_t v___y_400_; uint8_t v___y_401_; uint8_t v___y_402_; uint8_t v___x_417_; uint8_t v___y_419_; uint8_t v___y_420_; uint8_t v___y_421_; uint8_t v___y_423_; uint8_t v___x_435_; 
v___x_417_ = 2;
v___x_435_ = l_Lean_instBEqMessageSeverity_beq(v_severity_293_, v___x_417_);
if (v___x_435_ == 0)
{
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
uint8_t v___x_436_; 
lean_inc_ref(v_msgData_292_);
v___x_436_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_292_);
v___y_423_ = v___x_436_;
goto v___jp_422_;
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
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_346_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_346_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_346_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_346_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v_currNamespace_315_; lean_object* v_openDecls_316_; lean_object* v_env_317_; lean_object* v_messages_318_; lean_object* v_scopes_319_; lean_object* v_usedQuotCtxts_320_; lean_object* v_nextMacroScope_321_; lean_object* v_maxRecDepth_322_; lean_object* v_ngen_323_; lean_object* v_auxDeclNGen_324_; lean_object* v_infoState_325_; lean_object* v_traceState_326_; lean_object* v_snapshotTasks_327_; lean_object* v_prevLinterStates_328_; lean_object* v_codeQualityEntryTasks_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_345_; 
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
v_codeQualityEntryTasks_329_ = lean_ctor_get(v___x_314_, 12);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_345_ == 0)
{
v___x_331_ = v___x_314_;
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_codeQualityEntryTasks_329_);
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
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_345_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_currNamespace_315_);
lean_ctor_set(v___x_333_, 1, v_openDecls_316_);
v___x_334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___y_303_);
lean_inc_ref(v___y_300_);
lean_inc_ref(v___y_299_);
v___x_335_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_335_, 0, v___y_299_);
lean_ctor_set(v___x_335_, 1, v___y_302_);
lean_ctor_set(v___x_335_, 2, v___y_304_);
lean_ctor_set(v___x_335_, 3, v___y_300_);
lean_ctor_set(v___x_335_, 4, v___x_334_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*5, v___y_305_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*5 + 1, v___y_301_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*5 + 2, v_isSilent_294_);
v___x_336_ = l_Lean_MessageLog_add(v___x_335_, v_messages_318_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_336_);
v___x_338_ = v___x_331_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_env_317_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_scopes_319_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_usedQuotCtxts_320_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_nextMacroScope_321_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v_maxRecDepth_322_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_ngen_323_);
lean_ctor_set(v_reuseFailAlloc_344_, 7, v_auxDeclNGen_324_);
lean_ctor_set(v_reuseFailAlloc_344_, 8, v_infoState_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 9, v_traceState_326_);
lean_ctor_set(v_reuseFailAlloc_344_, 10, v_snapshotTasks_327_);
lean_ctor_set(v_reuseFailAlloc_344_, 11, v_prevLinterStates_328_);
lean_ctor_set(v_reuseFailAlloc_344_, 12, v_codeQualityEntryTasks_329_);
v___x_338_ = v_reuseFailAlloc_344_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_339_ = lean_st_ref_put(v___y_306_, v___x_338_);
v___x_340_ = lean_box(0);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_340_);
v___x_342_ = v___x_312_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_308_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec_ref(v___y_302_);
v_a_347_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_309_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_309_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec_ref(v___y_302_);
v_a_355_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_307_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_307_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
v___jp_363_:
{
lean_object* v_fileName_369_; lean_object* v_fileMap_370_; uint8_t v_suppressElabErrors_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_390_; 
v_fileName_369_ = lean_ctor_get(v___y_295_, 0);
v_fileMap_370_ = lean_ctor_get(v___y_295_, 1);
v_suppressElabErrors_371_ = lean_ctor_get_uint8(v___y_295_, sizeof(void*)*10);
v___x_372_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_292_);
v___x_373_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v___x_372_, v___y_296_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_inc_ref_n(v_fileMap_370_, 2);
v___x_378_ = l_Lean_FileMap_toPosition(v_fileMap_370_, v___y_365_);
lean_dec(v___y_365_);
v___x_379_ = l_Lean_FileMap_toPosition(v_fileMap_370_, v___y_368_);
lean_dec(v___y_368_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___closed__0));
if (v_suppressElabErrors_371_ == 0)
{
lean_del_object(v___x_376_);
v___y_299_ = v_fileName_369_;
v___y_300_ = v___x_381_;
v___y_301_ = v___y_366_;
v___y_302_ = v___x_378_;
v___y_303_ = v_a_374_;
v___y_304_ = v___x_380_;
v___y_305_ = v___y_367_;
v___y_306_ = v___y_296_;
goto v___jp_298_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___f_384_; uint8_t v___x_385_; 
v___x_382_ = lean_box(v_suppressElabErrors_371_);
v___x_383_ = lean_box(v___y_364_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_384_, 0, v___x_382_);
lean_closure_set(v___f_384_, 1, v___x_383_);
lean_inc(v_a_374_);
v___x_385_ = l_Lean_MessageData_hasTag(v___f_384_, v_a_374_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec_ref_known(v___x_380_, 1);
lean_dec_ref(v___x_378_);
lean_dec(v_a_374_);
v___x_386_ = lean_box(0);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_del_object(v___x_376_);
v___y_299_ = v_fileName_369_;
v___y_300_ = v___x_381_;
v___y_301_ = v___y_366_;
v___y_302_ = v___x_378_;
v___y_303_ = v_a_374_;
v___y_304_ = v___x_380_;
v___y_305_ = v___y_367_;
v___y_306_ = v___y_296_;
goto v___jp_298_;
}
}
}
}
v___jp_391_:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Syntax_getTailPos_x3f(v___y_393_, v___y_395_);
lean_dec(v___y_393_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_inc(v___y_396_);
v___y_364_ = v___y_392_;
v___y_365_ = v___y_396_;
v___y_366_ = v___y_394_;
v___y_367_ = v___y_395_;
v___y_368_ = v___y_396_;
goto v___jp_363_;
}
else
{
lean_object* v_val_398_; 
v_val_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v___x_397_, 1);
v___y_364_ = v___y_392_;
v___y_365_ = v___y_396_;
v___y_366_ = v___y_394_;
v___y_367_ = v___y_395_;
v___y_368_ = v_val_398_;
goto v___jp_363_;
}
}
v___jp_399_:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Command_getRef___redArg(v___y_295_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v_ref_405_; lean_object* v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v_ref_405_ = l_Lean_replaceRef(v_ref_291_, v_a_404_);
lean_dec(v_a_404_);
v___x_406_ = l_Lean_Syntax_getPos_x3f(v_ref_405_, v___y_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___y_392_ = v___y_400_;
v___y_393_ = v_ref_405_;
v___y_394_ = v___y_402_;
v___y_395_ = v___y_401_;
v___y_396_ = v___x_407_;
goto v___jp_391_;
}
else
{
lean_object* v_val_408_; 
v_val_408_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___x_406_, 1);
v___y_392_ = v___y_400_;
v___y_393_ = v_ref_405_;
v___y_394_ = v___y_402_;
v___y_395_ = v___y_401_;
v___y_396_ = v_val_408_;
goto v___jp_391_;
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec_ref(v_msgData_292_);
v_a_409_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_403_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_403_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
v___jp_418_:
{
if (v___y_421_ == 0)
{
v___y_400_ = v___y_419_;
v___y_401_ = v___y_420_;
v___y_402_ = v_severity_293_;
goto v___jp_399_;
}
else
{
v___y_400_ = v___y_419_;
v___y_401_ = v___y_420_;
v___y_402_ = v___x_417_;
goto v___jp_399_;
}
}
v___jp_422_:
{
if (v___y_423_ == 0)
{
lean_object* v___x_424_; lean_object* v_scopes_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_opts_428_; uint8_t v___x_429_; uint8_t v___x_430_; 
v___x_424_ = lean_st_ref_get(v___y_296_);
v_scopes_425_ = lean_ctor_get(v___x_424_, 2);
lean_inc(v_scopes_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_427_ = l_List_head_x21___redArg(v___x_426_, v_scopes_425_);
lean_dec(v_scopes_425_);
v_opts_428_ = lean_ctor_get(v___x_427_, 1);
lean_inc_ref(v_opts_428_);
lean_dec(v___x_427_);
v___x_429_ = 1;
v___x_430_ = l_Lean_instBEqMessageSeverity_beq(v_severity_293_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec_ref(v_opts_428_);
v___y_419_ = v___y_423_;
v___y_420_ = v___y_423_;
v___y_421_ = v___x_430_;
goto v___jp_418_;
}
else
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = l_Lean_warningAsError;
v___x_432_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__8(v_opts_428_, v___x_431_);
lean_dec_ref(v_opts_428_);
v___y_419_ = v___y_423_;
v___y_420_ = v___y_423_;
v___y_421_ = v___x_432_;
goto v___jp_418_;
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v_msgData_292_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_437_, lean_object* v_msgData_438_, lean_object* v_severity_439_, lean_object* v_isSilent_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v_severity_boxed_444_; uint8_t v_isSilent_boxed_445_; lean_object* v_res_446_; 
v_severity_boxed_444_ = lean_unbox(v_severity_439_);
v_isSilent_boxed_445_ = lean_unbox(v_isSilent_440_);
v_res_446_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_437_, v_msgData_438_, v_severity_boxed_444_, v_isSilent_boxed_445_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v_ref_437_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(lean_object* v_ref_447_, lean_object* v_msgData_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = 1;
v___x_453_ = 0;
v___x_454_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4(v_ref_447_, v_msgData_448_, v___x_452_, v___x_453_, v___y_449_, v___y_450_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3___boxed(lean_object* v_ref_455_, lean_object* v_msgData_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_ref_455_, v_msgData_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_ref_455_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__0));
v___x_463_ = l_Lean_stringToMessageData(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__2));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(lean_object* v_linterOption_467_, lean_object* v_stx_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_name_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_491_; 
v_name_473_ = lean_ctor_get(v_linterOption_467_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_linterOption_467_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_linterOption_467_, 1);
lean_dec(v_unused_492_);
v___x_475_ = v_linterOption_467_;
v_isShared_476_ = v_isSharedCheck_491_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_name_473_);
lean_dec(v_linterOption_467_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_491_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_477_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__1);
lean_inc(v_name_473_);
v___x_478_ = l_Lean_MessageData_ofName(v_name_473_);
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 7);
lean_ctor_set(v___x_475_, 1, v___x_478_);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_490_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_disable_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_481_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___closed__3);
v___x_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v_disable_483_ = l_Lean_MessageData_note(v___x_482_);
v___x_484_ = l_Lean_Linter_linterMessageTag;
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v_msg_469_);
lean_ctor_set(v___x_485_, 1, v_disable_483_);
v___x_486_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_487_, 0, v_name_473_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
lean_inc(v_stx_468_);
v___x_488_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_488_, 0, v_stx_468_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3(v_stx_468_, v___x_488_, v___y_470_, v___y_471_);
lean_dec(v_stx_468_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2___boxed(lean_object* v_linterOption_493_, lean_object* v_stx_494_, lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v_linterOption_493_, v_stx_494_, v_msg_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__0));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__2));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__4));
v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(lean_object* v___x_509_, uint8_t v___x_510_, lean_object* v___x_511_, lean_object* v_as_x27_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
if (lean_obj_tag(v_as_x27_512_) == 0)
{
lean_object* v___x_517_; 
lean_dec(v___x_511_);
lean_dec_ref(v___x_509_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_b_513_);
return v___x_517_;
}
else
{
lean_object* v_head_518_; lean_object* v_tail_519_; uint8_t v___x_520_; 
v_head_518_ = lean_ctor_get(v_as_x27_512_, 0);
v_tail_519_ = lean_ctor_get(v_as_x27_512_, 1);
v___x_520_ = l_Lean_NameSet_contains(v_b_513_, v_head_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
lean_inc_n(v_head_518_, 2);
v___x_521_ = l_Lean_NameSet_insert(v_b_513_, v_head_518_);
lean_inc_ref(v___x_509_);
v___x_522_ = l_Lean_Environment_contains(v___x_509_, v_head_518_, v___x_510_);
if (v___x_522_ == 0)
{
v_as_x27_512_ = v_tail_519_;
v_b_513_ = v___x_521_;
goto _start;
}
else
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_Linter_InternalModule_isInternalDecl(v_head_518_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Elab_Command_getRef___redArg(v___y_514_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_528_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__1);
lean_inc(v_head_518_);
v___x_529_ = l_Lean_MessageData_ofConstName(v_head_518_, v___x_524_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__3);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_inc(v___x_511_);
v___x_533_ = l_Lean_MessageData_ofName(v___x_511_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___closed__5);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2(v___x_527_, v_a_526_, v___x_536_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_dec_ref_known(v___x_537_, 1);
v_as_x27_512_ = v_tail_519_;
v_b_513_ = v___x_521_;
goto _start;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v___x_521_);
lean_dec(v___x_511_);
lean_dec_ref(v___x_509_);
v_a_539_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___x_521_);
lean_dec(v___x_511_);
lean_dec_ref(v___x_509_);
v_a_547_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_525_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_525_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
v_as_x27_512_ = v_tail_519_;
v_b_513_ = v___x_521_;
goto _start;
}
}
}
else
{
v_as_x27_512_ = v_tail_519_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg___boxed(lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_as_x27_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___x_8371__boxed_565_; lean_object* v_res_566_; 
v___x_8371__boxed_565_ = lean_unbox(v___x_558_);
v_res_566_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_557_, v___x_8371__boxed_565_, v___x_559_, v_as_x27_560_, v_b_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v_as_x27_560_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(lean_object* v___x_567_, uint8_t v___x_568_, lean_object* v___x_569_, lean_object* v_as_570_, size_t v_sz_571_, size_t v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_572_, v_sz_571_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v___x_569_);
lean_dec_ref(v___x_567_);
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
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_583_ = lean_array_uget_borrowed(v_as_570_, v_i_572_);
lean_inc(v_a_583_);
v___x_584_ = l_Lean_Linter_getNewDecls(v_a_583_);
lean_inc(v___x_569_);
lean_inc_ref(v___x_567_);
v___x_585_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_567_, v___x_568_, v___x_569_, v___x_584_, v_snd_579_, v___y_574_, v___y_575_);
lean_dec(v___x_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_box(0);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_a_586_);
lean_ctor_set(v___x_581_, 0, v___x_587_);
v___x_589_ = v___x_581_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_a_586_);
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
lean_dec_ref(v___x_567_);
v_a_594_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_585_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_585_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_as_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___x_8479__boxed_614_; size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v___x_8479__boxed_614_ = lean_unbox(v___x_605_);
v_sz_boxed_615_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_616_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_604_, v___x_8479__boxed_614_, v___x_606_, v_as_607_, v_sz_boxed_615_, v_i_boxed_616_, v_b_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_as_607_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(lean_object* v___x_618_, uint8_t v___x_619_, lean_object* v___x_620_, lean_object* v_as_621_, size_t v_sz_622_, size_t v_i_623_, lean_object* v_b_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v___x_620_);
lean_dec_ref(v___x_618_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_624_);
return v___x_629_;
}
else
{
lean_object* v_snd_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_653_; 
v_snd_630_ = lean_ctor_get(v_b_624_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_b_624_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_b_624_, 0);
lean_dec(v_unused_654_);
v___x_632_ = v_b_624_;
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snd_630_);
lean_dec(v_b_624_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_634_ = lean_array_uget_borrowed(v_as_621_, v_i_623_);
lean_inc(v_a_634_);
v___x_635_ = l_Lean_Linter_getNewDecls(v_a_634_);
lean_inc(v___x_620_);
lean_inc_ref(v___x_618_);
v___x_636_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_618_, v___x_619_, v___x_620_, v___x_635_, v_snd_630_, v___y_625_, v___y_626_);
lean_dec(v___x_635_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = lean_box(0);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v_a_637_);
lean_ctor_set(v___x_632_, 0, v___x_638_);
v___x_640_ = v___x_632_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_a_637_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_623_, v___x_641_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7_spec__11(v___x_618_, v___x_619_, v___x_620_, v_as_621_, v_sz_622_, v___x_642_, v___x_640_, v___y_625_, v___y_626_);
return v___x_643_;
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_del_object(v___x_632_);
lean_dec(v___x_620_);
lean_dec_ref(v___x_618_);
v_a_645_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_636_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_636_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7___boxed(lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v_as_658_, lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_b_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
uint8_t v___x_8547__boxed_665_; size_t v_sz_boxed_666_; size_t v_i_boxed_667_; lean_object* v_res_668_; 
v___x_8547__boxed_665_ = lean_unbox(v___x_656_);
v_sz_boxed_666_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_667_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_655_, v___x_8547__boxed_665_, v___x_657_, v_as_658_, v_sz_boxed_666_, v_i_boxed_667_, v_b_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_as_658_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(lean_object* v___x_669_, uint8_t v___x_670_, lean_object* v___x_671_, lean_object* v_as_672_, size_t v_sz_673_, size_t v_i_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = lean_usize_dec_lt(v_i_674_, v_sz_673_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v___x_671_);
lean_dec_ref(v___x_669_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_b_675_);
return v___x_680_;
}
else
{
lean_object* v_snd_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_704_; 
v_snd_681_ = lean_ctor_get(v_b_675_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_b_675_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_b_675_, 0);
lean_dec(v_unused_705_);
v___x_683_ = v_b_675_;
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_snd_681_);
lean_dec(v_b_675_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_704_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_685_ = lean_array_uget_borrowed(v_as_672_, v_i_674_);
lean_inc(v_a_685_);
v___x_686_ = l_Lean_Linter_getNewDecls(v_a_685_);
lean_inc(v___x_671_);
lean_inc_ref(v___x_669_);
v___x_687_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_669_, v___x_670_, v___x_671_, v___x_686_, v_snd_681_, v___y_676_, v___y_677_);
lean_dec(v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = lean_box(0);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v_a_688_);
lean_ctor_set(v___x_683_, 0, v___x_689_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_688_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_674_, v___x_692_);
v_i_674_ = v___x_693_;
v_b_675_ = v___x_691_;
goto _start;
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_683_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_669_);
v_a_696_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_as_709_, lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_8615__boxed_716_; size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v___x_8615__boxed_716_ = lean_unbox(v___x_707_);
v_sz_boxed_717_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_718_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_706_, v___x_8615__boxed_716_, v___x_708_, v_as_709_, v_sz_boxed_717_, v_i_boxed_718_, v_b_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec_ref(v_as_709_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(lean_object* v___x_720_, uint8_t v___x_721_, lean_object* v___x_722_, lean_object* v_as_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec(v___x_722_);
lean_dec_ref(v___x_720_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_b_726_);
return v___x_731_;
}
else
{
lean_object* v_snd_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_755_; 
v_snd_732_ = lean_ctor_get(v_b_726_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_b_726_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_b_726_, 0);
lean_dec(v_unused_756_);
v___x_734_ = v_b_726_;
v_isShared_735_ = v_isSharedCheck_755_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snd_732_);
lean_dec(v_b_726_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_755_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_a_736_ = lean_array_uget_borrowed(v_as_723_, v_i_725_);
lean_inc(v_a_736_);
v___x_737_ = l_Lean_Linter_getNewDecls(v_a_736_);
lean_inc(v___x_722_);
lean_inc_ref(v___x_720_);
v___x_738_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_720_, v___x_721_, v___x_722_, v___x_737_, v_snd_732_, v___y_727_, v___y_728_);
lean_dec(v___x_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_box(0);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_739_);
lean_ctor_set(v___x_734_, 0, v___x_740_);
v___x_742_ = v___x_734_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_a_739_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_add(v_i_725_, v___x_743_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9_spec__12(v___x_720_, v___x_721_, v___x_722_, v_as_723_, v_sz_724_, v___x_744_, v___x_742_, v___y_727_, v___y_728_);
return v___x_745_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_del_object(v___x_734_);
lean_dec(v___x_722_);
lean_dec_ref(v___x_720_);
v_a_747_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_738_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_738_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v___x_759_, lean_object* v_as_760_, lean_object* v_sz_761_, lean_object* v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v___x_8683__boxed_767_; size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v___x_8683__boxed_767_ = lean_unbox(v___x_758_);
v_sz_boxed_768_ = lean_unbox_usize(v_sz_761_);
lean_dec(v_sz_761_);
v_i_boxed_769_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_757_, v___x_8683__boxed_767_, v___x_759_, v_as_760_, v_sz_boxed_768_, v_i_boxed_769_, v_b_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_as_760_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(lean_object* v_init_771_, lean_object* v___x_772_, uint8_t v___x_773_, lean_object* v___x_774_, lean_object* v_n_775_, lean_object* v_b_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
if (lean_obj_tag(v_n_775_) == 0)
{
lean_object* v_cs_780_; lean_object* v___x_781_; lean_object* v___x_782_; size_t v_sz_783_; size_t v___x_784_; lean_object* v___x_785_; 
v_cs_780_ = lean_ctor_get(v_n_775_, 0);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_b_776_);
v_sz_783_ = lean_array_size(v_cs_780_);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_771_, v___x_772_, v___x_773_, v___x_774_, v_cs_780_, v_sz_783_, v___x_784_, v___x_782_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_800_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_800_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_fst_790_; 
v_fst_790_ = lean_ctor_get(v_a_786_, 0);
if (lean_obj_tag(v_fst_790_) == 0)
{
lean_object* v_snd_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v_snd_791_ = lean_ctor_get(v_a_786_, 1);
lean_inc(v_snd_791_);
lean_dec(v_a_786_);
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v_snd_791_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_792_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
else
{
lean_object* v_val_796_; lean_object* v___x_798_; 
lean_inc_ref(v_fst_790_);
lean_dec(v_a_786_);
v_val_796_ = lean_ctor_get(v_fst_790_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v_fst_790_, 1);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_val_796_);
v___x_798_ = v___x_788_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_val_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_785_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_785_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_vs_809_; lean_object* v___x_810_; lean_object* v___x_811_; size_t v_sz_812_; size_t v___x_813_; lean_object* v___x_814_; 
v_vs_809_ = lean_ctor_get(v_n_775_, 0);
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_b_776_);
v_sz_812_ = lean_array_size(v_vs_809_);
v___x_813_ = ((size_t)0ULL);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__9(v___x_772_, v___x_773_, v___x_774_, v_vs_809_, v_sz_812_, v___x_813_, v___x_811_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_829_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_829_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_829_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_829_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_fst_819_; 
v_fst_819_ = lean_ctor_get(v_a_815_, 0);
if (lean_obj_tag(v_fst_819_) == 0)
{
lean_object* v_snd_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v_snd_820_ = lean_ctor_get(v_a_815_, 1);
lean_inc(v_snd_820_);
lean_dec(v_a_815_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_snd_820_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_object* v_val_825_; lean_object* v___x_827_; 
lean_inc_ref(v_fst_819_);
lean_dec(v_a_815_);
v_val_825_ = lean_ctor_get(v_fst_819_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v_fst_819_, 1);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_val_825_);
v___x_827_ = v___x_817_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_val_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_814_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_814_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(lean_object* v_init_838_, lean_object* v___x_839_, uint8_t v___x_840_, lean_object* v___x_841_, lean_object* v_as_842_, size_t v_sz_843_, size_t v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_lt(v_i_844_, v_sz_843_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v___x_841_);
lean_dec_ref(v___x_839_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_b_845_);
return v___x_850_;
}
else
{
lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_885_; 
v_snd_851_ = lean_ctor_get(v_b_845_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_b_845_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_b_845_, 0);
lean_dec(v_unused_886_);
v___x_853_ = v_b_845_;
v_isShared_854_ = v_isSharedCheck_885_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_dec(v_b_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_885_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_array_uget_borrowed(v_as_842_, v_i_844_);
lean_inc(v_snd_851_);
lean_inc(v___x_841_);
lean_inc_ref(v___x_839_);
v___x_856_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_838_, v___x_839_, v___x_840_, v___x_841_, v_a_855_, v_snd_851_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_876_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_876_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_876_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_876_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
if (lean_obj_tag(v_a_857_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec(v___x_841_);
lean_dec_ref(v___x_839_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_a_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_861_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_snd_851_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_863_);
v___x_865_ = v___x_859_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_del_object(v___x_859_);
lean_dec(v_snd_851_);
v_a_868_ = lean_ctor_get(v_a_857_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v_a_857_, 1);
v___x_869_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v_a_868_);
lean_ctor_set(v___x_853_, 0, v___x_869_);
v___x_871_ = v___x_853_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_868_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
size_t v___x_872_; size_t v___x_873_; 
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_844_, v___x_872_);
v_i_844_ = v___x_873_;
v_b_845_ = v___x_871_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_del_object(v___x_853_);
lean_dec(v_snd_851_);
lean_dec(v___x_841_);
lean_dec_ref(v___x_839_);
v_a_877_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_856_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_856_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v_as_891_, lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v___x_8751__boxed_898_; size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v___x_8751__boxed_898_ = lean_unbox(v___x_889_);
v_sz_boxed_899_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_900_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6_spec__8(v_init_887_, v___x_888_, v___x_8751__boxed_898_, v___x_890_, v_as_891_, v_sz_boxed_899_, v_i_boxed_900_, v_b_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_as_891_);
lean_dec(v_init_887_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6___boxed(lean_object* v_init_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_n_906_, lean_object* v_b_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v___x_8773__boxed_911_; lean_object* v_res_912_; 
v___x_8773__boxed_911_ = lean_unbox(v___x_904_);
v_res_912_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_902_, v___x_903_, v___x_8773__boxed_911_, v___x_905_, v_n_906_, v_b_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_n_906_);
lean_dec(v_init_902_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(lean_object* v___x_913_, uint8_t v___x_914_, lean_object* v___x_915_, lean_object* v_t_916_, lean_object* v_init_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_root_921_; lean_object* v_tail_922_; lean_object* v___x_923_; 
v_root_921_ = lean_ctor_get(v_t_916_, 0);
v_tail_922_ = lean_ctor_get(v_t_916_, 1);
lean_inc(v___x_915_);
lean_inc_ref(v___x_913_);
lean_inc(v_init_917_);
v___x_923_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__6(v_init_917_, v___x_913_, v___x_914_, v___x_915_, v_root_921_, v_init_917_, v___y_918_, v___y_919_);
lean_dec(v_init_917_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_960_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_960_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_960_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_960_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
if (lean_obj_tag(v_a_924_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; 
lean_dec(v___x_915_);
lean_dec_ref(v___x_913_);
v_a_928_ = lean_ctor_get(v_a_924_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v_a_924_, 1);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_a_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; size_t v_sz_935_; size_t v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_926_);
v_a_932_ = lean_ctor_get(v_a_924_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v_a_924_, 1);
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v_a_932_);
v_sz_935_ = lean_array_size(v_tail_922_);
v___x_936_ = ((size_t)0ULL);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4_spec__7(v___x_913_, v___x_914_, v___x_915_, v_tail_922_, v_sz_935_, v___x_936_, v___x_934_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_951_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_951_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_951_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_951_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_fst_942_; 
v_fst_942_ = lean_ctor_get(v_a_938_, 0);
if (lean_obj_tag(v_fst_942_) == 0)
{
lean_object* v_snd_943_; lean_object* v___x_945_; 
v_snd_943_ = lean_ctor_get(v_a_938_, 1);
lean_inc(v_snd_943_);
lean_dec(v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_snd_943_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_snd_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
lean_object* v_val_947_; lean_object* v___x_949_; 
lean_inc_ref(v_fst_942_);
lean_dec(v_a_938_);
v_val_947_ = lean_ctor_get(v_fst_942_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v_fst_942_, 1);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_val_947_);
v___x_949_ = v___x_940_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_val_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_937_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_937_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v___x_915_);
lean_dec_ref(v___x_913_);
v_a_961_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_923_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_923_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4___boxed(lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v_t_972_, lean_object* v_init_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_8964__boxed_977_; lean_object* v_res_978_; 
v___x_8964__boxed_977_ = lean_unbox(v___x_970_);
v_res_978_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v___x_969_, v___x_8964__boxed_977_, v___x_971_, v_t_972_, v_init_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec_ref(v_t_972_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(lean_object* v_o_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_env_983_; lean_object* v___x_984_; lean_object* v_toEnvExtension_985_; lean_object* v_asyncMode_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_merged_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v___x_982_ = lean_st_ref_get(v___y_980_);
v_env_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_982_);
v___x_984_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_985_ = lean_ctor_get(v___x_984_, 0);
v_asyncMode_986_ = lean_ctor_get(v_toEnvExtension_985_, 2);
v___x_987_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_988_ = lean_box(0);
v___x_989_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_987_, v___x_984_, v_env_983_, v_asyncMode_986_, v___x_988_);
v_merged_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_989_, 1);
lean_dec(v_unused_999_);
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_merged_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_merged_990_);
lean_ctor_set(v___x_992_, 0, v_o_979_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_o_979_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_merged_990_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1000_, v___y_1001_);
lean_dec(v___y_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v_scopes_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_opts_1011_; lean_object* v___x_1012_; 
v___x_1007_ = lean_st_ref_get(v___y_1005_);
v_scopes_1008_ = lean_ctor_get(v___x_1007_, 2);
lean_inc(v_scopes_1008_);
lean_dec(v___x_1007_);
v___x_1009_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1010_ = l_List_head_x21___redArg(v___x_1009_, v_scopes_1008_);
lean_dec(v_scopes_1008_);
v_opts_1011_ = lean_ctor_get(v___x_1010_, 1);
lean_inc_ref(v_opts_1011_);
lean_dec(v___x_1010_);
v___x_1012_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_opts_1011_, v___y_1005_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0___boxed(lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_messages_1022_; uint8_t v___x_1023_; 
v___x_1021_ = lean_st_ref_get(v___y_1019_);
v_messages_1022_ = lean_ctor_get(v___x_1021_, 1);
lean_inc_ref(v_messages_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Lean_MessageLog_hasErrors(v_messages_1022_);
lean_dec_ref(v_messages_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1064_; 
v___x_1024_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0(v___y_1018_, v___y_1019_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1064_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1064_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = l_Lean_Linter_linter_coreInternal_internalModule;
v___x_1030_ = l_Lean_Linter_getLinterValue(v___x_1029_, v_a_1025_);
lean_dec(v_a_1025_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1031_);
v___x_1033_ = v___x_1027_;
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
else
{
lean_object* v___x_1035_; lean_object* v_env_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1035_ = lean_st_ref_get(v___y_1019_);
v_env_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc_ref(v_env_1036_);
lean_dec(v___x_1035_);
v___x_1037_ = l_Lean_Environment_mainModule(v_env_1036_);
v___x_1038_ = l_Lean_Linter_InternalModule_isInternalModule(v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v___x_1037_);
lean_dec_ref(v_env_1036_);
v___x_1039_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1039_);
v___x_1041_ = v___x_1027_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_del_object(v___x_1027_);
v___x_1043_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__1___redArg(v___y_1019_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = l_Lean_NameSet_empty;
v___x_1046_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__4(v_env_1036_, v___x_1038_, v___x_1037_, v_a_1044_, v___x_1045_, v___y_1018_, v___y_1019_);
lean_dec(v_a_1044_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1046_, 0);
lean_dec(v_unused_1055_);
v___x_1048_ = v___x_1046_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v___x_1046_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1046_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1046_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_InternalModule_internalModuleLinter___lam__0___boxed(lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Linter_InternalModule_internalModuleLinter___lam__0(v_x_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v_x_1067_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(lean_object* v_o_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___redArg(v_o_1086_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0___boxed(lean_object* v_o_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__0_spec__0(v_o_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(lean_object* v___x_1096_, uint8_t v___x_1097_, lean_object* v___x_1098_, lean_object* v_as_1099_, lean_object* v_as_x27_1100_, lean_object* v_b_1101_, lean_object* v_a_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___redArg(v___x_1096_, v___x_1097_, v___x_1098_, v_as_x27_1100_, v_b_1101_, v___y_1103_, v___y_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3___boxed(lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_as_1110_, lean_object* v_as_x27_1111_, lean_object* v_b_1112_, lean_object* v_a_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___x_9276__boxed_1117_; lean_object* v_res_1118_; 
v___x_9276__boxed_1117_ = lean_unbox(v___x_1108_);
v_res_1118_ = l_List_forIn_x27_loop___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__3(v___x_1107_, v___x_9276__boxed_1117_, v___x_1109_, v_as_1110_, v_as_x27_1111_, v_b_1112_, v_a_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v_as_x27_1111_);
lean_dec(v_as_1110_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_msgData_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___redArg(v_msgData_1119_, v___y_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_msgData_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_InternalModule_internalModuleLinter_spec__2_spec__3_spec__4_spec__7(v_msgData_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_Linter_InternalModule_internalModuleLinter));
v___x_1131_ = l_Lean_Elab_Command_addLinter(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2____boxed(lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Linter_InternalModule_0__Lean_Linter_InternalModule_initFn_00___x40_Lean_Linter_InternalModule_2150894783____hygCtx___hyg_2_();
return v_res_1133_;
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
