// Lean compiler output
// Module: Lean.Linter.Extra.DupNamespace
// Imports: public import Lean.Elab.Command public import Lean.Linter.Basic
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dupNamespace"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(100, 70, 92, 151, 235, 189, 126, 126)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the duplicated namespace linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(204, 219, 14, 12, 236, 190, 241, 203)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_dupNamespace;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value;
static const lean_string_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 73, 228, 195, 89, 60, 49, 127)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "The namespace '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' is duplicated in the declaration '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value;
static const lean_closure_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__0_value)} };
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value;
static const lean_closure_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value)} };
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value;
static const lean_string_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "DupNamespaceLinter"};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 209, 81, 27, 145, 227, 71, 229)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 197, 181, 132, 231, 73, 118, 142)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0(lean_object* v_toPure_64_, lean_object* v_____do__lift_65_){
_start:
{
lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_66_ = lean_ctor_get(v_____do__lift_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v_____do__lift_65_);
v___x_67_ = lean_apply_2(v_toPure_64_, lean_box(0), v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1(lean_object* v_toPure_68_, lean_object* v_____s_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_apply_2(v_toPure_68_, lean_box(0), v_____s_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(lean_object* v_fm_71_, lean_object* v_pos_72_, lean_object* v_toPure_73_, lean_object* v_a_74_, lean_object* v_b_75_, lean_object* v_c_76_){
_start:
{
lean_object* v_range_77_; lean_object* v_selectionRange_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_100_; 
v_range_77_ = lean_ctor_get(v_b_75_, 0);
v_selectionRange_78_ = lean_ctor_get(v_b_75_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_b_75_);
if (v_isSharedCheck_100_ == 0)
{
v___x_80_ = v_b_75_;
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_selectionRange_78_);
lean_inc(v_range_77_);
lean_dec(v_b_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_pos_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_pos_82_ = lean_ctor_get(v_range_77_, 0);
lean_inc_ref(v_pos_82_);
lean_dec_ref(v_range_77_);
v___x_83_ = l_Lean_FileMap_ofPosition(v_fm_71_, v_pos_82_);
v___x_84_ = lean_nat_dec_le(v_pos_72_, v___x_83_);
lean_dec(v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_del_object(v___x_80_);
lean_dec_ref(v_selectionRange_78_);
lean_dec(v_a_74_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_c_76_);
v___x_86_ = lean_apply_2(v_toPure_73_, lean_box(0), v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_pos_87_; lean_object* v_endPos_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v_pos_87_ = lean_ctor_get(v_selectionRange_78_, 0);
lean_inc_ref(v_pos_87_);
v_endPos_88_ = lean_ctor_get(v_selectionRange_78_, 2);
lean_inc_ref(v_endPos_88_);
lean_dec_ref(v_selectionRange_78_);
v___x_89_ = l_Lean_FileMap_ofPosition(v_fm_71_, v_pos_87_);
v___x_90_ = l_Lean_FileMap_ofPosition(v_fm_71_, v_endPos_88_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_90_);
lean_ctor_set(v___x_80_, 0, v___x_89_);
v___x_92_ = v___x_80_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_99_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = l_Lean_Syntax_ofRange(v___x_92_, v___x_84_);
v___x_94_ = 0;
v___x_95_ = l_Lean_mkIdentFrom(v___x_93_, v_a_74_, v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_array_push(v_c_76_, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___x_98_ = lean_apply_2(v_toPure_73_, lean_box(0), v___x_97_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(lean_object* v_fm_101_, lean_object* v_pos_102_, lean_object* v_toPure_103_, lean_object* v_a_104_, lean_object* v_b_105_, lean_object* v_c_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(v_fm_101_, v_pos_102_, v_toPure_103_, v_a_104_, v_b_105_, v_c_106_);
lean_dec(v_pos_102_);
lean_dec_ref(v_fm_101_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(lean_object* v_pos_110_, lean_object* v_toPure_111_, lean_object* v_inst_112_, lean_object* v_drs_113_, lean_object* v_toBind_114_, lean_object* v___f_115_, lean_object* v___f_116_, lean_object* v_fm_117_){
_start:
{
lean_object* v___f_118_; lean_object* v_nms_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_118_, 0, v_fm_117_);
lean_closure_set(v___f_118_, 1, v_pos_110_);
lean_closure_set(v___f_118_, 2, v_toPure_111_);
v_nms_119_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_120_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_112_, v___f_118_, v_nms_119_, v_drs_113_);
lean_inc(v_toBind_114_);
v___x_121_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v___x_120_, v___f_115_);
v___x_122_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v___x_121_, v___f_116_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4(lean_object* v___x_123_, lean_object* v_pos_124_, lean_object* v_toPure_125_, lean_object* v_inst_126_, lean_object* v_toBind_127_, lean_object* v___f_128_, lean_object* v___f_129_, lean_object* v_inst_130_, lean_object* v_____do__lift_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_drs_135_; lean_object* v___f_136_; lean_object* v___x_137_; 
v___x_132_ = l_Lean_declRangeExt;
v___x_133_ = lean_box(1);
v___x_134_ = lean_box(0);
v_drs_135_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_123_, v___x_132_, v_____do__lift_131_, v___x_133_, v___x_134_);
lean_inc(v_toBind_127_);
v___f_136_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3), 8, 7);
lean_closure_set(v___f_136_, 0, v_pos_124_);
lean_closure_set(v___f_136_, 1, v_toPure_125_);
lean_closure_set(v___f_136_, 2, v_inst_126_);
lean_closure_set(v___f_136_, 3, v_drs_135_);
lean_closure_set(v___f_136_, 4, v_toBind_127_);
lean_closure_set(v___f_136_, 5, v___f_128_);
lean_closure_set(v___f_136_, 6, v___f_129_);
v___x_137_ = lean_apply_4(v_toBind_127_, lean_box(0), lean_box(0), v_inst_130_, v___f_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_pos_141_){
_start:
{
lean_object* v_toApplicative_142_; lean_object* v_toBind_143_; lean_object* v_getEnv_144_; lean_object* v_toPure_145_; lean_object* v___x_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v_toApplicative_142_ = lean_ctor_get(v_inst_138_, 0);
v_toBind_143_ = lean_ctor_get(v_inst_138_, 1);
lean_inc_n(v_toBind_143_, 2);
v_getEnv_144_ = lean_ctor_get(v_inst_139_, 0);
lean_inc(v_getEnv_144_);
lean_dec_ref(v_inst_139_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_142_, 1);
lean_inc_n(v_toPure_145_, 3);
v___x_146_ = lean_box(1);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_147_, 0, v_toPure_145_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_148_, 0, v_toPure_145_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4), 9, 8);
lean_closure_set(v___f_149_, 0, v___x_146_);
lean_closure_set(v___f_149_, 1, v_pos_141_);
lean_closure_set(v___f_149_, 2, v_toPure_145_);
lean_closure_set(v___f_149_, 3, v_inst_138_);
lean_closure_set(v___f_149_, 4, v_toBind_143_);
lean_closure_set(v___f_149_, 5, v___f_147_);
lean_closure_set(v___f_149_, 6, v___f_148_);
lean_closure_set(v___f_149_, 7, v_inst_140_);
v___x_150_ = lean_apply_4(v_toBind_143_, lean_box(0), lean_box(0), v_getEnv_144_, v___f_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom(lean_object* v_m_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_pos_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(v_inst_152_, v_inst_153_, v_inst_154_, v_pos_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(uint8_t v___x_157_, lean_object* v_currNamespace_158_, lean_object* v_toPure_159_, lean_object* v_a_160_, lean_object* v_x_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___y_166_; lean_object* v___x_173_; 
v___x_163_ = l_Lean_TSyntax_getId(v_a_160_);
v___x_164_ = 0;
v___x_173_ = l_Lean_Syntax_getRange_x3f(v_a_160_, v___x_164_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_166_ = v___x_174_;
goto v___jp_165_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_173_, 1);
v___y_166_ = v_val_175_;
goto v___jp_165_;
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_167_ = l_Lean_Syntax_ofRange(v___y_166_, v___x_157_);
v___x_168_ = l_Lean_Name_append(v_currNamespace_158_, v___x_163_);
v___x_169_ = l_Lean_mkIdentFrom(v___x_167_, v___x_168_, v___x_164_);
lean_dec(v___x_167_);
v___x_170_ = lean_array_push(v___y_162_, v___x_169_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = lean_apply_2(v_toPure_159_, lean_box(0), v___x_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed(lean_object* v___x_176_, lean_object* v_currNamespace_177_, lean_object* v_toPure_178_, lean_object* v_a_179_, lean_object* v_x_180_, lean_object* v___y_181_){
_start:
{
uint8_t v___x_301__boxed_182_; lean_object* v_res_183_; 
v___x_301__boxed_182_ = lean_unbox(v___x_176_);
v_res_183_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(v___x_301__boxed_182_, v_currNamespace_177_, v_toPure_178_, v_a_179_, v_x_180_, v___y_181_);
lean_dec(v_a_179_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(uint8_t v___x_184_, lean_object* v_toPure_185_, lean_object* v_ids_186_, lean_object* v_inst_187_, lean_object* v_aliases_188_, lean_object* v_toBind_189_, lean_object* v___f_190_, lean_object* v_currNamespace_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___f_193_; size_t v_sz_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_192_ = lean_box(v___x_184_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_193_, 0, v___x_192_);
lean_closure_set(v___f_193_, 1, v_currNamespace_191_);
lean_closure_set(v___f_193_, 2, v_toPure_185_);
v_sz_194_ = lean_array_size(v_ids_186_);
v___x_195_ = ((size_t)0ULL);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_187_, v_ids_186_, v___f_193_, v_sz_194_, v___x_195_, v_aliases_188_);
v___x_197_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v___x_196_, v___f_190_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed(lean_object* v___x_198_, lean_object* v_toPure_199_, lean_object* v_ids_200_, lean_object* v_inst_201_, lean_object* v_aliases_202_, lean_object* v_toBind_203_, lean_object* v___f_204_, lean_object* v_currNamespace_205_){
_start:
{
uint8_t v___x_336__boxed_206_; lean_object* v_res_207_; 
v___x_336__boxed_206_ = lean_unbox(v___x_198_);
v_res_207_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(v___x_336__boxed_206_, v_toPure_199_, v_ids_200_, v_inst_201_, v_aliases_202_, v_toBind_203_, v___f_204_, v_currNamespace_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_stx_218_){
_start:
{
lean_object* v_toApplicative_219_; lean_object* v_toBind_220_; lean_object* v_toPure_221_; lean_object* v_aliases_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_toApplicative_219_ = lean_ctor_get(v_inst_216_, 0);
v_toBind_220_ = lean_ctor_get(v_inst_216_, 1);
lean_inc(v_toBind_220_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_inc(v_toPure_221_);
v_aliases_222_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_223_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_218_);
v___x_224_ = l_Lean_Syntax_isOfKind(v_stx_218_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v_toBind_220_);
lean_dec(v_stx_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_216_);
v___x_225_ = lean_apply_2(v_toPure_221_, lean_box(0), v_aliases_222_);
return v___x_225_;
}
else
{
lean_object* v_getCurrNamespace_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_ids_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; 
v_getCurrNamespace_226_ = lean_ctor_get(v_inst_217_, 0);
lean_inc(v_getCurrNamespace_226_);
lean_dec_ref(v_inst_217_);
lean_inc(v_toPure_221_);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_227_, 0, v_toPure_221_);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = l_Lean_Syntax_getArg(v_stx_218_, v___x_228_);
lean_dec(v_stx_218_);
v_ids_230_ = l_Lean_Syntax_getArgs(v___x_229_);
lean_dec(v___x_229_);
v___x_231_ = lean_box(v___x_224_);
lean_inc(v_toBind_220_);
v___f_232_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_232_, 0, v___x_231_);
lean_closure_set(v___f_232_, 1, v_toPure_221_);
lean_closure_set(v___f_232_, 2, v_ids_230_);
lean_closure_set(v___f_232_, 3, v_inst_216_);
lean_closure_set(v___f_232_, 4, v_aliases_222_);
lean_closure_set(v___f_232_, 5, v_toBind_220_);
lean_closure_set(v___f_232_, 6, v___f_227_);
v___x_233_ = lean_apply_4(v_toBind_220_, lean_box(0), lean_box(0), v_getCurrNamespace_226_, v___f_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(lean_object* v_m_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_stx_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(v_inst_235_, v_inst_236_, v_stx_237_);
return v___x_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
v___x_241_ = l_Lean_Syntax_isOfKind(v_x_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(v_x_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object* v___x_245_, lean_object* v_pos_246_, lean_object* v_init_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_d_251_; 
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v_l_256_; lean_object* v_r_257_; lean_object* v___x_258_; lean_object* v_a_259_; 
v_k_254_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_k_254_);
v_v_255_ = lean_ctor_get(v_x_248_, 2);
lean_inc(v_v_255_);
v_l_256_ = lean_ctor_get(v_x_248_, 3);
lean_inc(v_l_256_);
v_r_257_ = lean_ctor_get(v_x_248_, 4);
lean_inc(v_r_257_);
lean_dec_ref_known(v_x_248_, 5);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_245_, v_pos_246_, v_init_247_, v_l_256_);
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
if (lean_obj_tag(v_a_259_) == 0)
{
lean_object* v_a_260_; 
lean_dec_ref(v___x_258_);
lean_dec(v_r_257_);
lean_dec(v_v_255_);
lean_dec(v_k_254_);
v_a_260_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v_a_259_, 1);
v_d_251_ = v_a_260_;
goto v___jp_250_;
}
else
{
lean_object* v_range_261_; lean_object* v_a_262_; lean_object* v_selectionRange_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_286_; 
v_range_261_ = lean_ctor_get(v_v_255_, 0);
lean_inc_ref(v_range_261_);
v_a_262_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v_a_259_, 1);
v_selectionRange_263_ = lean_ctor_get(v_v_255_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_v_255_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_v_255_, 0);
lean_dec(v_unused_287_);
v___x_265_ = v_v_255_;
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_selectionRange_263_);
lean_dec(v_v_255_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_pos_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_pos_267_ = lean_ctor_get(v_range_261_, 0);
lean_inc_ref(v_pos_267_);
lean_dec_ref(v_range_261_);
v___x_268_ = l_Lean_FileMap_ofPosition(v___x_245_, v_pos_267_);
v___x_269_ = lean_nat_dec_le(v_pos_246_, v___x_268_);
lean_dec(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v_a_270_; 
lean_del_object(v___x_265_);
lean_dec_ref(v_selectionRange_263_);
lean_dec(v_a_262_);
lean_dec(v_k_254_);
v_a_270_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_270_);
lean_dec_ref(v___x_258_);
if (lean_obj_tag(v_a_270_) == 0)
{
lean_object* v_a_271_; 
lean_dec(v_r_257_);
v_a_271_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v_a_270_, 1);
v_d_251_ = v_a_271_;
goto v___jp_250_;
}
else
{
lean_object* v_a_272_; 
v_a_272_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v_a_270_, 1);
v_init_247_ = v_a_272_;
v_x_248_ = v_r_257_;
goto _start;
}
}
else
{
lean_object* v_pos_274_; lean_object* v_endPos_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec_ref(v___x_258_);
v_pos_274_ = lean_ctor_get(v_selectionRange_263_, 0);
lean_inc_ref(v_pos_274_);
v_endPos_275_ = lean_ctor_get(v_selectionRange_263_, 2);
lean_inc_ref(v_endPos_275_);
lean_dec_ref(v_selectionRange_263_);
v___x_276_ = l_Lean_FileMap_ofPosition(v___x_245_, v_pos_274_);
v___x_277_ = l_Lean_FileMap_ofPosition(v___x_245_, v_endPos_275_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_277_);
lean_ctor_set(v___x_265_, 0, v___x_276_);
v___x_279_ = v___x_265_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_285_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = l_Lean_Syntax_ofRange(v___x_279_, v___x_269_);
v___x_281_ = 0;
v___x_282_ = l_Lean_mkIdentFrom(v___x_280_, v_k_254_, v___x_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_array_push(v_a_262_, v___x_282_);
v_init_247_ = v___x_283_;
v_x_248_ = v_r_257_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_init_247_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
v___jp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_d_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object* v___x_290_, lean_object* v_pos_291_, lean_object* v_init_292_, lean_object* v_x_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_290_, v_pos_291_, v_init_292_, v_x_293_);
lean_dec(v_pos_291_);
lean_dec_ref(v___x_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object* v_pos_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; lean_object* v_env_301_; lean_object* v_fileMap_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_drs_307_; lean_object* v_nms_308_; lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
v___x_300_ = lean_st_ref_get(v___y_298_);
v_env_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_ref(v_env_301_);
lean_dec(v___x_300_);
v_fileMap_302_ = lean_ctor_get(v___y_297_, 1);
v___x_303_ = lean_box(1);
v___x_304_ = l_Lean_declRangeExt;
v___x_305_ = lean_box(1);
v___x_306_ = lean_box(0);
v_drs_307_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_303_, v___x_304_, v_env_301_, v___x_305_, v___x_306_);
v_nms_308_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_309_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_302_, v_pos_296_, v_nms_308_, v_drs_307_);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_a_314_; lean_object* v___x_316_; 
v_a_314_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_a_314_);
lean_dec(v_a_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_a_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object* v_pos_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v_pos_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v_pos_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v_head_326_; lean_object* v_tail_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; uint8_t v___x_330_; 
v_head_326_ = lean_ctor_get(v_x_324_, 0);
v_tail_327_ = lean_ctor_get(v_x_324_, 1);
v_fst_328_ = lean_ctor_get(v_head_326_, 0);
v_snd_329_ = lean_ctor_get(v_head_326_, 1);
v___x_330_ = lean_name_eq(v_fst_328_, v_snd_329_);
if (v___x_330_ == 0)
{
v_x_324_ = v_tail_327_;
goto _start;
}
else
{
lean_object* v___x_332_; 
lean_inc(v_head_326_);
v___x_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_332_, 0, v_head_326_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_x_333_);
lean_dec(v_x_333_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_335_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
lean_ctor_set(v___x_340_, 4, v___x_338_);
lean_ctor_set(v___x_340_, 5, v___x_338_);
lean_ctor_set(v___x_340_, 6, v___x_338_);
lean_ctor_set(v___x_340_, 7, v___x_338_);
lean_ctor_set(v___x_340_, 8, v___x_338_);
lean_ctor_set(v___x_340_, 9, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(32u);
v___x_342_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4(void){
_start:
{
size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((size_t)5ULL);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_unsigned_to_nat(32u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__3);
v___x_349_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_345_);
lean_ctor_set(v___x_349_, 3, v___x_345_);
lean_ctor_set_usize(v___x_349_, 4, v___x_344_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_box(1);
v___x_351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__4);
v___x_352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__1);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(lean_object* v_msgData_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_env_358_; lean_object* v___x_359_; lean_object* v_scopes_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_opts_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_357_ = lean_st_ref_get(v___y_355_);
v_env_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_env_358_);
lean_dec(v___x_357_);
v___x_359_ = lean_st_ref_get(v___y_355_);
v_scopes_360_ = lean_ctor_get(v___x_359_, 2);
lean_inc(v_scopes_360_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_362_ = l_List_head_x21___redArg(v___x_361_, v_scopes_360_);
lean_dec(v_scopes_360_);
v_opts_363_ = lean_ctor_get(v___x_362_, 1);
lean_inc_ref(v_opts_363_);
lean_dec(v___x_362_);
v___x_364_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__2);
v___x_365_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___closed__5);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_358_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_ctor_set(v___x_366_, 3, v_opts_363_);
v___x_367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_msgData_354_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v_msgData_369_, v___y_370_);
lean_dec(v___y_370_);
return v_res_372_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_opts_373_, lean_object* v_opt_374_){
_start:
{
lean_object* v_name_375_; lean_object* v_defValue_376_; lean_object* v_map_377_; lean_object* v___x_378_; 
v_name_375_ = lean_ctor_get(v_opt_374_, 0);
v_defValue_376_ = lean_ctor_get(v_opt_374_, 1);
v_map_377_ = lean_ctor_get(v_opts_373_, 0);
v___x_378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_377_, v_name_375_);
if (lean_obj_tag(v___x_378_) == 0)
{
uint8_t v___x_379_; 
v___x_379_ = lean_unbox(v_defValue_376_);
return v___x_379_;
}
else
{
lean_object* v_val_380_; 
v_val_380_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_378_, 1);
if (lean_obj_tag(v_val_380_) == 1)
{
uint8_t v_v_381_; 
v_v_381_ = lean_ctor_get_uint8(v_val_380_, 0);
lean_dec_ref_known(v_val_380_, 0);
return v_v_381_;
}
else
{
uint8_t v___x_382_; 
lean_dec(v_val_380_);
v___x_382_ = lean_unbox(v_defValue_376_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_opts_383_, lean_object* v_opt_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(v_opts_383_, v_opt_384_);
lean_dec_ref(v_opt_384_);
lean_dec_ref(v_opts_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0(uint8_t v___y_388_, uint8_t v_suppressElabErrors_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 1)
{
lean_object* v_pre_391_; 
v_pre_391_ = lean_ctor_get(v_x_390_, 0);
if (lean_obj_tag(v_pre_391_) == 0)
{
lean_object* v_str_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_str_392_ = lean_ctor_get(v_x_390_, 1);
v___x_393_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___closed__0));
v___x_394_ = lean_string_dec_eq(v_str_392_, v___x_393_);
if (v___x_394_ == 0)
{
return v___y_388_;
}
else
{
return v_suppressElabErrors_389_;
}
}
else
{
return v___y_388_;
}
}
else
{
return v___y_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___boxed(lean_object* v___y_395_, lean_object* v_suppressElabErrors_396_, lean_object* v_x_397_){
_start:
{
uint8_t v___y_7078__boxed_398_; uint8_t v_suppressElabErrors_boxed_399_; uint8_t v_res_400_; lean_object* v_r_401_; 
v___y_7078__boxed_398_ = lean_unbox(v___y_395_);
v_suppressElabErrors_boxed_399_ = lean_unbox(v_suppressElabErrors_396_);
v_res_400_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0(v___y_7078__boxed_398_, v_suppressElabErrors_boxed_399_, v_x_397_);
lean_dec(v_x_397_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(lean_object* v_ref_403_, lean_object* v_msgData_404_, uint8_t v_severity_405_, uint8_t v_isSilent_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; uint8_t v___y_414_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; uint8_t v___y_474_; uint8_t v___y_475_; uint8_t v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; uint8_t v___y_502_; uint8_t v___y_503_; uint8_t v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_510_; uint8_t v___y_511_; uint8_t v___y_512_; uint8_t v___x_527_; uint8_t v___y_529_; uint8_t v___y_530_; uint8_t v___y_531_; uint8_t v___y_533_; uint8_t v___x_545_; 
v___x_527_ = 2;
v___x_545_ = l_Lean_instBEqMessageSeverity_beq(v_severity_405_, v___x_527_);
if (v___x_545_ == 0)
{
v___y_533_ = v___x_545_;
goto v___jp_532_;
}
else
{
uint8_t v___x_546_; 
lean_inc_ref(v_msgData_404_);
v___x_546_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_404_);
v___y_533_ = v___x_546_;
goto v___jp_532_;
}
v___jp_410_:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Elab_Command_getScope___redArg(v___y_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = l_Lean_Elab_Command_getScope___redArg(v___y_418_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_456_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_456_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_456_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_456_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v_currNamespace_427_; lean_object* v_openDecls_428_; lean_object* v_env_429_; lean_object* v_messages_430_; lean_object* v_scopes_431_; lean_object* v_usedQuotCtxts_432_; lean_object* v_nextMacroScope_433_; lean_object* v_maxRecDepth_434_; lean_object* v_ngen_435_; lean_object* v_auxDeclNGen_436_; lean_object* v_infoState_437_; lean_object* v_traceState_438_; lean_object* v_snapshotTasks_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_455_; 
v___x_426_ = lean_st_ref_take(v___y_418_);
v_currNamespace_427_ = lean_ctor_get(v_a_420_, 2);
lean_inc(v_currNamespace_427_);
lean_dec(v_a_420_);
v_openDecls_428_ = lean_ctor_get(v_a_422_, 3);
lean_inc(v_openDecls_428_);
lean_dec(v_a_422_);
v_env_429_ = lean_ctor_get(v___x_426_, 0);
v_messages_430_ = lean_ctor_get(v___x_426_, 1);
v_scopes_431_ = lean_ctor_get(v___x_426_, 2);
v_usedQuotCtxts_432_ = lean_ctor_get(v___x_426_, 3);
v_nextMacroScope_433_ = lean_ctor_get(v___x_426_, 4);
v_maxRecDepth_434_ = lean_ctor_get(v___x_426_, 5);
v_ngen_435_ = lean_ctor_get(v___x_426_, 6);
v_auxDeclNGen_436_ = lean_ctor_get(v___x_426_, 7);
v_infoState_437_ = lean_ctor_get(v___x_426_, 8);
v_traceState_438_ = lean_ctor_get(v___x_426_, 9);
v_snapshotTasks_439_ = lean_ctor_get(v___x_426_, 10);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_455_ == 0)
{
v___x_441_ = v___x_426_;
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snapshotTasks_439_);
lean_inc(v_traceState_438_);
lean_inc(v_infoState_437_);
lean_inc(v_auxDeclNGen_436_);
lean_inc(v_ngen_435_);
lean_inc(v_maxRecDepth_434_);
lean_inc(v_nextMacroScope_433_);
lean_inc(v_usedQuotCtxts_432_);
lean_inc(v_scopes_431_);
lean_inc(v_messages_430_);
lean_inc(v_env_429_);
lean_dec(v___x_426_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_currNamespace_427_);
lean_ctor_set(v___x_443_, 1, v_openDecls_428_);
v___x_444_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___y_415_);
lean_inc_ref(v___y_413_);
lean_inc_ref(v___y_411_);
v___x_445_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_445_, 0, v___y_411_);
lean_ctor_set(v___x_445_, 1, v___y_412_);
lean_ctor_set(v___x_445_, 2, v___y_417_);
lean_ctor_set(v___x_445_, 3, v___y_413_);
lean_ctor_set(v___x_445_, 4, v___x_444_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*5, v___y_416_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*5 + 1, v___y_414_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*5 + 2, v_isSilent_406_);
v___x_446_ = l_Lean_MessageLog_add(v___x_445_, v_messages_430_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_446_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_env_429_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_scopes_431_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_usedQuotCtxts_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_nextMacroScope_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_maxRecDepth_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_ngen_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_auxDeclNGen_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_infoState_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 9, v_traceState_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 10, v_snapshotTasks_439_);
v___x_448_ = v_reuseFailAlloc_454_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_st_ref_set(v___y_418_, v___x_448_);
v___x_450_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_450_);
v___x_452_ = v___x_424_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_420_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v___y_412_);
v_a_457_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_421_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_421_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v___y_417_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v___y_412_);
v_a_465_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_419_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_419_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
v___jp_473_:
{
lean_object* v_fileName_479_; lean_object* v_fileMap_480_; uint8_t v_suppressElabErrors_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_500_; 
v_fileName_479_ = lean_ctor_get(v___y_407_, 0);
v_fileMap_480_ = lean_ctor_get(v___y_407_, 1);
v_suppressElabErrors_481_ = lean_ctor_get_uint8(v___y_407_, sizeof(void*)*10);
v___x_482_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_404_);
v___x_483_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v___x_482_, v___y_408_);
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_500_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_500_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc_ref_n(v_fileMap_480_, 2);
v___x_488_ = l_Lean_FileMap_toPosition(v_fileMap_480_, v___y_477_);
lean_dec(v___y_477_);
v___x_489_ = l_Lean_FileMap_toPosition(v_fileMap_480_, v___y_478_);
lean_dec(v___y_478_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
v___x_491_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___closed__0));
if (v_suppressElabErrors_481_ == 0)
{
lean_del_object(v___x_486_);
v___y_411_ = v_fileName_479_;
v___y_412_ = v___x_488_;
v___y_413_ = v___x_491_;
v___y_414_ = v___y_475_;
v___y_415_ = v_a_484_;
v___y_416_ = v___y_476_;
v___y_417_ = v___x_490_;
v___y_418_ = v___y_408_;
goto v___jp_410_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___f_494_; uint8_t v___x_495_; 
v___x_492_ = lean_box(v___y_474_);
v___x_493_ = lean_box(v_suppressElabErrors_481_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_494_, 0, v___x_492_);
lean_closure_set(v___f_494_, 1, v___x_493_);
lean_inc(v_a_484_);
v___x_495_ = l_Lean_MessageData_hasTag(v___f_494_, v_a_484_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec_ref_known(v___x_490_, 1);
lean_dec_ref(v___x_488_);
lean_dec(v_a_484_);
v___x_496_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_496_);
v___x_498_ = v___x_486_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_del_object(v___x_486_);
v___y_411_ = v_fileName_479_;
v___y_412_ = v___x_488_;
v___y_413_ = v___x_491_;
v___y_414_ = v___y_475_;
v___y_415_ = v_a_484_;
v___y_416_ = v___y_476_;
v___y_417_ = v___x_490_;
v___y_418_ = v___y_408_;
goto v___jp_410_;
}
}
}
}
v___jp_501_:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Syntax_getTailPos_x3f(v___y_505_, v___y_504_);
lean_dec(v___y_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_inc(v___y_506_);
v___y_474_ = v___y_502_;
v___y_475_ = v___y_503_;
v___y_476_ = v___y_504_;
v___y_477_ = v___y_506_;
v___y_478_ = v___y_506_;
goto v___jp_473_;
}
else
{
lean_object* v_val_508_; 
v_val_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_507_, 1);
v___y_474_ = v___y_502_;
v___y_475_ = v___y_503_;
v___y_476_ = v___y_504_;
v___y_477_ = v___y_506_;
v___y_478_ = v_val_508_;
goto v___jp_473_;
}
}
v___jp_509_:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Elab_Command_getRef___redArg(v___y_407_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v_ref_515_; lean_object* v___x_516_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v_ref_515_ = l_Lean_replaceRef(v_ref_403_, v_a_514_);
lean_dec(v_a_514_);
v___x_516_ = l_Lean_Syntax_getPos_x3f(v_ref_515_, v___y_511_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___y_502_ = v___y_510_;
v___y_503_ = v___y_512_;
v___y_504_ = v___y_511_;
v___y_505_ = v_ref_515_;
v___y_506_ = v___x_517_;
goto v___jp_501_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v___x_516_, 1);
v___y_502_ = v___y_510_;
v___y_503_ = v___y_512_;
v___y_504_ = v___y_511_;
v___y_505_ = v_ref_515_;
v___y_506_ = v_val_518_;
goto v___jp_501_;
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_msgData_404_);
v_a_519_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_513_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
v___jp_528_:
{
if (v___y_531_ == 0)
{
v___y_510_ = v___y_529_;
v___y_511_ = v___y_530_;
v___y_512_ = v_severity_405_;
goto v___jp_509_;
}
else
{
v___y_510_ = v___y_529_;
v___y_511_ = v___y_530_;
v___y_512_ = v___x_527_;
goto v___jp_509_;
}
}
v___jp_532_:
{
if (v___y_533_ == 0)
{
lean_object* v___x_534_; lean_object* v_scopes_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_opts_538_; uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_534_ = lean_st_ref_get(v___y_408_);
v_scopes_535_ = lean_ctor_get(v___x_534_, 2);
lean_inc(v_scopes_535_);
lean_dec(v___x_534_);
v___x_536_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_537_ = l_List_head_x21___redArg(v___x_536_, v_scopes_535_);
lean_dec(v_scopes_535_);
v_opts_538_ = lean_ctor_get(v___x_537_, 1);
lean_inc_ref(v_opts_538_);
lean_dec(v___x_537_);
v___x_539_ = 1;
v___x_540_ = l_Lean_instBEqMessageSeverity_beq(v_severity_405_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v_opts_538_);
v___y_529_ = v___y_533_;
v___y_530_ = v___y_533_;
v___y_531_ = v___x_540_;
goto v___jp_528_;
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = l_Lean_warningAsError;
v___x_542_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__12(v_opts_538_, v___x_541_);
lean_dec_ref(v_opts_538_);
v___y_529_ = v___y_533_;
v___y_530_ = v___y_533_;
v___y_531_ = v___x_542_;
goto v___jp_528_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_msgData_404_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_ref_547_, lean_object* v_msgData_548_, lean_object* v_severity_549_, lean_object* v_isSilent_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v_severity_boxed_554_; uint8_t v_isSilent_boxed_555_; lean_object* v_res_556_; 
v_severity_boxed_554_ = lean_unbox(v_severity_549_);
v_isSilent_boxed_555_ = lean_unbox(v_isSilent_550_);
v_res_556_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(v_ref_547_, v_msgData_548_, v_severity_boxed_554_, v_isSilent_boxed_555_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_ref_547_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(lean_object* v_ref_557_, lean_object* v_msgData_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
v___x_562_ = 1;
v___x_563_ = 0;
v___x_564_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9(v_ref_557_, v_msgData_558_, v___x_562_, v___x_563_, v___y_559_, v___y_560_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6___boxed(lean_object* v_ref_565_, lean_object* v_msgData_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(v_ref_565_, v_msgData_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v_ref_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__2));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(lean_object* v_linterOption_577_, lean_object* v_stx_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_name_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_601_; 
v_name_583_ = lean_ctor_get(v_linterOption_577_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_linterOption_577_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_linterOption_577_, 1);
lean_dec(v_unused_602_);
v___x_585_ = v_linterOption_577_;
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_name_583_);
lean_dec(v_linterOption_577_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_601_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__1);
lean_inc(v_name_583_);
v___x_588_ = l_Lean_MessageData_ofName(v_name_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 7);
lean_ctor_set(v___x_585_, 1, v___x_588_);
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_600_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_disable_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_591_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___closed__3);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v_disable_593_ = l_Lean_MessageData_note(v___x_592_);
v___x_594_ = l_Lean_Linter_linterMessageTag;
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v_msg_579_);
lean_ctor_set(v___x_595_, 1, v_disable_593_);
v___x_596_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_597_, 0, v_name_583_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
lean_inc(v_stx_578_);
v___x_598_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_598_, 0, v_stx_578_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6(v_stx_578_, v___x_598_, v___y_580_, v___y_581_);
lean_dec(v_stx_578_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(lean_object* v_linterOption_603_, lean_object* v_stx_604_, lean_object* v_msg_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_linterOption_603_, v_stx_604_, v_msg_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object* v_o_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; lean_object* v_env_614_; lean_object* v___x_615_; lean_object* v_toEnvExtension_616_; lean_object* v_asyncMode_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_merged_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v___x_613_ = lean_st_ref_get(v___y_611_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
v___x_615_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_616_ = lean_ctor_get(v___x_615_, 0);
v_asyncMode_617_ = lean_ctor_get(v_toEnvExtension_616_, 2);
v___x_618_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_619_ = lean_box(0);
v___x_620_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_618_, v___x_615_, v_env_614_, v_asyncMode_617_, v___x_619_);
v_merged_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_620_, 1);
lean_dec(v_unused_630_);
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_merged_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_merged_621_);
lean_ctor_set(v___x_623_, 0, v_o_610_);
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_o_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_merged_621_);
v___x_626_ = v_reuseFailAlloc_628_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object* v_o_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_631_, v___y_632_);
lean_dec(v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; lean_object* v_scopes_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_opts_642_; lean_object* v___x_643_; 
v___x_638_ = lean_st_ref_get(v___y_636_);
v_scopes_639_ = lean_ctor_get(v___x_638_, 2);
lean_inc(v_scopes_639_);
lean_dec(v___x_638_);
v___x_640_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_641_ = l_List_head_x21___redArg(v___x_640_, v_scopes_639_);
lean_dec(v_scopes_639_);
v_opts_642_ = lean_ctor_get(v___x_641_, 1);
lean_inc_ref(v_opts_642_);
lean_dec(v___x_641_);
v___x_643_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_opts_642_, v___y_636_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object* v_linterOption_648_, lean_object* v_stx_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_665_; 
v___x_654_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_651_, v___y_652_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_665_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_665_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_Linter_getLinterValue(v_linterOption_648_, v_a_655_);
lean_dec(v_a_655_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec_ref(v_msg_650_);
lean_dec(v_stx_649_);
lean_dec_ref(v_linterOption_648_);
v___x_660_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; 
lean_del_object(v___x_657_);
v___x_664_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_linterOption_648_, v_stx_649_, v_msg_650_, v___y_651_, v___y_652_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object* v_linterOption_666_, lean_object* v_stx_667_, lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_linterOption_666_, v_stx_667_, v_msg_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__4));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object* v_as_682_, size_t v_sz_683_, size_t v_i_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_a_690_; uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_b_685_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_696_ = lean_box(0);
v_a_697_ = lean_array_uget_borrowed(v_as_682_, v_i_684_);
v___x_698_ = l_Lean_Syntax_getId(v_a_697_);
v___x_699_ = l_Lean_Name_hasMacroScopes(v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_isPrivateName(v___x_698_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___y_704_; 
v___x_701_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
lean_inc(v___x_698_);
v___x_702_ = l_Lean_Name_components(v___x_698_);
if (lean_obj_tag(v___x_702_) == 0)
{
v___y_704_ = v___x_702_;
goto v___jp_703_;
}
else
{
lean_object* v_tail_726_; 
v_tail_726_ = lean_ctor_get(v___x_702_, 1);
lean_inc(v_tail_726_);
v___y_704_ = v_tail_726_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v___x_702_, v___y_704_);
v___x_706_ = l_List_find_x3f___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v___x_705_);
lean_dec(v___x_705_);
if (lean_obj_tag(v___x_706_) == 1)
{
lean_object* v_val_707_; lean_object* v_fst_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_706_, 1);
v_fst_708_ = lean_ctor_get(v_val_707_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_val_707_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_val_707_, 1);
lean_dec(v_unused_725_);
v___x_710_ = v_val_707_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_fst_708_);
lean_dec(v_val_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
v___x_713_ = l_Lean_MessageData_ofName(v_fst_708_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 7);
lean_ctor_set(v___x_710_, 1, v___x_713_);
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_723_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_MessageData_ofName(v___x_698_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__5);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
lean_inc(v_a_697_);
v___x_722_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_701_, v_a_697_, v___x_721_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_dec_ref_known(v___x_722_, 1);
v_a_690_ = v___x_696_;
goto v___jp_689_;
}
else
{
return v___x_722_;
}
}
}
}
else
{
lean_dec(v___x_706_);
lean_dec(v___x_698_);
v_a_690_ = v___x_696_;
goto v___jp_689_;
}
}
}
else
{
lean_dec(v___x_698_);
v_a_690_ = v___x_696_;
goto v___jp_689_;
}
}
else
{
lean_dec(v___x_698_);
v_a_690_ = v___x_696_;
goto v___jp_689_;
}
}
v___jp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_684_, v___x_691_);
v_i_684_ = v___x_692_;
v_b_685_ = v_a_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(lean_object* v_as_727_, lean_object* v_sz_728_, lean_object* v_i_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_735_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v_as_727_, v_sz_boxed_734_, v_i_boxed_735_, v_b_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v_as_727_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(uint8_t v___x_737_, lean_object* v___x_738_, lean_object* v_as_739_, size_t v_sz_740_, size_t v_i_741_, lean_object* v_b_742_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_lt(v_i_741_, v_sz_740_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_dec(v___x_738_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_b_742_);
return v___x_745_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___y_750_; lean_object* v___x_758_; 
v_a_746_ = lean_array_uget_borrowed(v_as_739_, v_i_741_);
v___x_747_ = l_Lean_TSyntax_getId(v_a_746_);
v___x_748_ = 0;
v___x_758_ = l_Lean_Syntax_getRange_x3f(v_a_746_, v___x_748_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_750_ = v___x_759_;
goto v___jp_749_;
}
else
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v___x_758_, 1);
v___y_750_ = v_val_760_;
goto v___jp_749_;
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; size_t v___x_755_; size_t v___x_756_; 
v___x_751_ = l_Lean_Syntax_ofRange(v___y_750_, v___x_737_);
lean_inc(v___x_738_);
v___x_752_ = l_Lean_Name_append(v___x_738_, v___x_747_);
v___x_753_ = l_Lean_mkIdentFrom(v___x_751_, v___x_752_, v___x_748_);
lean_dec(v___x_751_);
v___x_754_ = lean_array_push(v_b_742_, v___x_753_);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_741_, v___x_755_);
v_i_741_ = v___x_756_;
v_b_742_ = v___x_754_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg___boxed(lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_as_763_, lean_object* v_sz_764_, lean_object* v_i_765_, lean_object* v_b_766_, lean_object* v___y_767_){
_start:
{
uint8_t v___x_7623__boxed_768_; size_t v_sz_boxed_769_; size_t v_i_boxed_770_; lean_object* v_res_771_; 
v___x_7623__boxed_768_ = lean_unbox(v___x_761_);
v_sz_boxed_769_ = lean_unbox_usize(v_sz_764_);
lean_dec(v_sz_764_);
v_i_boxed_770_ = lean_unbox_usize(v_i_765_);
lean_dec(v_i_765_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_7623__boxed_768_, v___x_762_, v_as_763_, v_sz_boxed_769_, v_i_boxed_770_, v_b_766_);
lean_dec_ref(v_as_763_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object* v_stx_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_aliases_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_aliases_776_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_777_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_772_);
v___x_778_ = l_Lean_Syntax_isOfKind(v_stx_772_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v_stx_772_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_aliases_776_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Elab_Command_getScope___redArg(v___y_774_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_currNamespace_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_ids_785_; size_t v_sz_786_; size_t v___x_787_; lean_object* v___x_788_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v_currNamespace_782_ = lean_ctor_get(v_a_781_, 2);
lean_inc(v_currNamespace_782_);
lean_dec(v_a_781_);
v___x_783_ = lean_unsigned_to_nat(3u);
v___x_784_ = l_Lean_Syntax_getArg(v_stx_772_, v___x_783_);
lean_dec(v_stx_772_);
v_ids_785_ = l_Lean_Syntax_getArgs(v___x_784_);
lean_dec(v___x_784_);
v_sz_786_ = lean_array_size(v_ids_785_);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_778_, v_currNamespace_782_, v_ids_785_, v_sz_786_, v___x_787_, v_aliases_776_);
lean_dec_ref(v_ids_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
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
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_788_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_788_);
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
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_stx_772_);
v_a_805_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_780_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_780_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___boxed(lean_object* v_stx_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v_stx_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(lean_object* v___f_818_, lean_object* v_stx_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v_aliases_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___x_859_; lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_883_; 
v___x_859_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_820_, v___y_821_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_883_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_883_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_883_;
goto v_resetjp_861_;
}
v___jp_823_:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v___y_827_, v___y_826_, v___y_825_);
lean_dec(v___y_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v___x_831_; size_t v_sz_832_; size_t v___x_833_; lean_object* v___x_834_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v___x_830_ = l_Array_append___redArg(v_a_829_, v___y_824_);
lean_dec_ref(v___y_824_);
v___x_831_ = lean_box(0);
v_sz_832_ = lean_array_size(v___x_830_);
v___x_833_ = ((size_t)0ULL);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_830_, v_sz_832_, v___x_833_, v___x_831_, v___y_826_, v___y_825_);
lean_dec_ref(v___x_830_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_842_);
v___x_836_ = v___x_834_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___x_834_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_831_);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_831_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
return v___x_834_;
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v___y_824_);
v_a_843_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_828_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_828_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
v___jp_851_:
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 0;
v___x_856_ = l_Lean_Syntax_getPos_x3f(v_stx_819_, v___x_855_);
lean_dec(v_stx_819_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_857_; 
v___x_857_ = lean_unsigned_to_nat(0u);
v___y_824_ = v_aliases_852_;
v___y_825_ = v___y_854_;
v___y_826_ = v___y_853_;
v___y_827_ = v___x_857_;
goto v___jp_823_;
}
else
{
lean_object* v_val_858_; 
v_val_858_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_856_, 1);
v___y_824_ = v_aliases_852_;
v___y_825_ = v___y_854_;
v___y_826_ = v___y_853_;
v___y_827_ = v_val_858_;
goto v___jp_823_;
}
}
v_resetjp_861_:
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
v___x_865_ = l_Lean_Linter_getLinterValue(v___x_864_, v_a_860_);
lean_dec(v_a_860_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec(v_stx_819_);
lean_dec_ref(v___f_818_);
v___x_866_ = lean_box(0);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_870_; 
lean_del_object(v___x_862_);
lean_inc(v_stx_819_);
v___x_870_ = l_Lean_Syntax_find_x3f(v_stx_819_, v___f_818_);
if (lean_obj_tag(v___x_870_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_872_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v_val_871_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v_aliases_852_ = v_a_873_;
v___y_853_ = v___y_820_;
v___y_854_ = v___y_821_;
goto v___jp_851_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_stx_819_);
v_a_874_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_872_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_872_);
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
else
{
lean_object* v___x_882_; 
lean_dec(v___x_870_);
v___x_882_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v_aliases_852_ = v___x_882_;
v___y_853_ = v___y_820_;
v___y_854_ = v___y_821_;
goto v___jp_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(lean_object* v___f_884_, lean_object* v_stx_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(v___f_884_, v_stx_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object* v_o_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_906_, v___y_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object* v_o_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(v_o_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object* v___x_916_, lean_object* v_pos_917_, lean_object* v_init_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_916_, v_pos_917_, v_init_918_, v_x_919_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object* v___x_924_, lean_object* v_pos_925_, lean_object* v_init_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(v___x_924_, v_pos_925_, v_init_926_, v_x_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_pos_925_);
lean_dec_ref(v___x_924_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8(uint8_t v___x_932_, lean_object* v___x_933_, lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___redArg(v___x_932_, v___x_933_, v_as_934_, v_sz_935_, v_i_936_, v_b_937_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8___boxed(lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v_as_944_, lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_7969__boxed_951_; size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v___x_7969__boxed_951_ = lean_unbox(v___x_942_);
v_sz_boxed_952_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_953_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5_spec__8(v___x_7969__boxed_951_, v___x_943_, v_as_944_, v_sz_boxed_952_, v_i_boxed_953_, v_b_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_as_944_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11(lean_object* v_msgData_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___redArg(v_msgData_955_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11___boxed(lean_object* v_msgData_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__6_spec__9_spec__11(v_msgData_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace));
v___x_967_ = l_Lean_Elab_Command_addLinter(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
return v_res_969_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2998168599____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_dupNamespace = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_dupNamespace);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_DupNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Extra_DupNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Extra_DupNamespace(builtin);
}
#ifdef __cplusplus
}
#endif
