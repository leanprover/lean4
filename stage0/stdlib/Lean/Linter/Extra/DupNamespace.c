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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dupNamespace"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(100, 70, 92, 151, 235, 189, 126, 126)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the duplicated namespace linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(204, 219, 14, 12, 236, 190, 241, 203)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_dupNamespace;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "consecutiveOnly"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(100, 70, 92, 151, 235, 189, 126, 126)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(133, 203, 110, 203, 110, 115, 227, 16)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "only warn on consecutive duplicated namespaces"};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(204, 219, 14, 12, 236, 190, 241, 203)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value_aux_5),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 121, 163, 79, 184, 131, 172, 11)}};
static const lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_dupNamespace_consecutiveOnly;
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
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 73, 228, 195, 89, 60, 49, 127)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0 = (const lean_object*)&l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "The namespace `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` is duplicated in the declaration `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "The namespaces "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = " are duplicated in the declaration `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 209, 81, 27, 145, 227, 71, 229)}};
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 197, 181, 132, 231, 73, 118, 142)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_86_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_87_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_88_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4__spec__0(v___x_85_, v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4____boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0(lean_object* v_toPure_91_, lean_object* v_____do__lift_92_){
_start:
{
lean_object* v_a_93_; lean_object* v___x_94_; 
v_a_93_ = lean_ctor_get(v_____do__lift_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref(v_____do__lift_92_);
v___x_94_ = lean_apply_2(v_toPure_91_, lean_box(0), v_a_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1(lean_object* v_toPure_95_, lean_object* v_____s_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_2(v_toPure_95_, lean_box(0), v_____s_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(lean_object* v_fm_98_, lean_object* v_pos_99_, lean_object* v_toPure_100_, lean_object* v_a_101_, lean_object* v_b_102_, lean_object* v_c_103_){
_start:
{
lean_object* v_range_104_; lean_object* v_selectionRange_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_127_; 
v_range_104_ = lean_ctor_get(v_b_102_, 0);
v_selectionRange_105_ = lean_ctor_get(v_b_102_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_b_102_);
if (v_isSharedCheck_127_ == 0)
{
v___x_107_ = v_b_102_;
v_isShared_108_ = v_isSharedCheck_127_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_selectionRange_105_);
lean_inc(v_range_104_);
lean_dec(v_b_102_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_127_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_pos_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_pos_109_ = lean_ctor_get(v_range_104_, 0);
lean_inc_ref(v_pos_109_);
lean_dec_ref(v_range_104_);
v___x_110_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_pos_109_);
v___x_111_ = lean_nat_dec_le(v_pos_99_, v___x_110_);
lean_dec(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_del_object(v___x_107_);
lean_dec_ref(v_selectionRange_105_);
lean_dec(v_a_101_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_c_103_);
v___x_113_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_112_);
return v___x_113_;
}
else
{
lean_object* v_pos_114_; lean_object* v_endPos_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v_pos_114_ = lean_ctor_get(v_selectionRange_105_, 0);
lean_inc_ref(v_pos_114_);
v_endPos_115_ = lean_ctor_get(v_selectionRange_105_, 2);
lean_inc_ref(v_endPos_115_);
lean_dec_ref(v_selectionRange_105_);
v___x_116_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_pos_114_);
v___x_117_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_endPos_115_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_117_);
lean_ctor_set(v___x_107_, 0, v___x_116_);
v___x_119_ = v___x_107_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_126_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_120_ = l_Lean_Syntax_ofRange(v___x_119_, v___x_111_);
v___x_121_ = 0;
v___x_122_ = l_Lean_mkIdentFrom(v___x_120_, v_a_101_, v___x_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_array_push(v_c_103_, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___x_125_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_124_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(lean_object* v_fm_128_, lean_object* v_pos_129_, lean_object* v_toPure_130_, lean_object* v_a_131_, lean_object* v_b_132_, lean_object* v_c_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(v_fm_128_, v_pos_129_, v_toPure_130_, v_a_131_, v_b_132_, v_c_133_);
lean_dec(v_pos_129_);
lean_dec_ref(v_fm_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(lean_object* v_pos_137_, lean_object* v_toPure_138_, lean_object* v_inst_139_, lean_object* v_drs_140_, lean_object* v_toBind_141_, lean_object* v___f_142_, lean_object* v___f_143_, lean_object* v_fm_144_){
_start:
{
lean_object* v___f_145_; lean_object* v_nms_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_145_, 0, v_fm_144_);
lean_closure_set(v___f_145_, 1, v_pos_137_);
lean_closure_set(v___f_145_, 2, v_toPure_138_);
v_nms_146_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_147_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_139_, v___f_145_, v_nms_146_, v_drs_140_);
lean_inc(v_toBind_141_);
v___x_148_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v___x_147_, v___f_142_);
v___x_149_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v___x_148_, v___f_143_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4(lean_object* v___x_150_, lean_object* v_pos_151_, lean_object* v_toPure_152_, lean_object* v_inst_153_, lean_object* v_toBind_154_, lean_object* v___f_155_, lean_object* v___f_156_, lean_object* v_inst_157_, lean_object* v_____do__lift_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_drs_162_; lean_object* v___f_163_; lean_object* v___x_164_; 
v___x_159_ = l_Lean_declRangeExt;
v___x_160_ = lean_box(1);
v___x_161_ = lean_box(0);
v_drs_162_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_150_, v___x_159_, v_____do__lift_158_, v___x_160_, v___x_161_);
lean_inc(v_toBind_154_);
v___f_163_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3), 8, 7);
lean_closure_set(v___f_163_, 0, v_pos_151_);
lean_closure_set(v___f_163_, 1, v_toPure_152_);
lean_closure_set(v___f_163_, 2, v_inst_153_);
lean_closure_set(v___f_163_, 3, v_drs_162_);
lean_closure_set(v___f_163_, 4, v_toBind_154_);
lean_closure_set(v___f_163_, 5, v___f_155_);
lean_closure_set(v___f_163_, 6, v___f_156_);
v___x_164_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v_inst_157_, v___f_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_pos_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toBind_170_; lean_object* v_getEnv_171_; lean_object* v_toPure_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_165_, 0);
v_toBind_170_ = lean_ctor_get(v_inst_165_, 1);
lean_inc_n(v_toBind_170_, 2);
v_getEnv_171_ = lean_ctor_get(v_inst_166_, 0);
lean_inc(v_getEnv_171_);
lean_dec_ref(v_inst_166_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc_n(v_toPure_172_, 3);
v___x_173_ = lean_box(1);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_174_, 0, v_toPure_172_);
v___f_175_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_175_, 0, v_toPure_172_);
v___f_176_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4), 9, 8);
lean_closure_set(v___f_176_, 0, v___x_173_);
lean_closure_set(v___f_176_, 1, v_pos_168_);
lean_closure_set(v___f_176_, 2, v_toPure_172_);
lean_closure_set(v___f_176_, 3, v_inst_165_);
lean_closure_set(v___f_176_, 4, v_toBind_170_);
lean_closure_set(v___f_176_, 5, v___f_174_);
lean_closure_set(v___f_176_, 6, v___f_175_);
lean_closure_set(v___f_176_, 7, v_inst_167_);
v___x_177_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v_getEnv_171_, v___f_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom(lean_object* v_m_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_pos_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(v_inst_179_, v_inst_180_, v_inst_181_, v_pos_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(uint8_t v___x_184_, lean_object* v_currNamespace_185_, lean_object* v_toPure_186_, lean_object* v_a_187_, lean_object* v_x_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___y_193_; lean_object* v___x_200_; 
v___x_190_ = l_Lean_TSyntax_getId(v_a_187_);
v___x_191_ = 0;
v___x_200_ = l_Lean_Syntax_getRange_x3f(v_a_187_, v___x_191_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_193_ = v___x_201_;
goto v___jp_192_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_200_, 1);
v___y_193_ = v_val_202_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_194_ = l_Lean_Syntax_ofRange(v___y_193_, v___x_184_);
v___x_195_ = l_Lean_Name_append(v_currNamespace_185_, v___x_190_);
v___x_196_ = l_Lean_mkIdentFrom(v___x_194_, v___x_195_, v___x_191_);
lean_dec(v___x_194_);
v___x_197_ = lean_array_push(v___y_189_, v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = lean_apply_2(v_toPure_186_, lean_box(0), v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed(lean_object* v___x_203_, lean_object* v_currNamespace_204_, lean_object* v_toPure_205_, lean_object* v_a_206_, lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
uint8_t v___x_301__boxed_209_; lean_object* v_res_210_; 
v___x_301__boxed_209_ = lean_unbox(v___x_203_);
v_res_210_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(v___x_301__boxed_209_, v_currNamespace_204_, v_toPure_205_, v_a_206_, v_x_207_, v___y_208_);
lean_dec(v_a_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(uint8_t v___x_211_, lean_object* v_toPure_212_, lean_object* v_ids_213_, lean_object* v_inst_214_, lean_object* v_aliases_215_, lean_object* v_toBind_216_, lean_object* v___f_217_, lean_object* v_currNamespace_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___f_220_; size_t v_sz_221_; size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = lean_box(v___x_211_);
v___f_220_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_220_, 0, v___x_219_);
lean_closure_set(v___f_220_, 1, v_currNamespace_218_);
lean_closure_set(v___f_220_, 2, v_toPure_212_);
v_sz_221_ = lean_array_size(v_ids_213_);
v___x_222_ = ((size_t)0ULL);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_214_, v_ids_213_, v___f_220_, v_sz_221_, v___x_222_, v_aliases_215_);
v___x_224_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_223_, v___f_217_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed(lean_object* v___x_225_, lean_object* v_toPure_226_, lean_object* v_ids_227_, lean_object* v_inst_228_, lean_object* v_aliases_229_, lean_object* v_toBind_230_, lean_object* v___f_231_, lean_object* v_currNamespace_232_){
_start:
{
uint8_t v___x_336__boxed_233_; lean_object* v_res_234_; 
v___x_336__boxed_233_ = lean_unbox(v___x_225_);
v_res_234_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(v___x_336__boxed_233_, v_toPure_226_, v_ids_227_, v_inst_228_, v_aliases_229_, v_toBind_230_, v___f_231_, v_currNamespace_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_stx_245_){
_start:
{
lean_object* v_toApplicative_246_; lean_object* v_toBind_247_; lean_object* v_toPure_248_; lean_object* v_aliases_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_toApplicative_246_ = lean_ctor_get(v_inst_243_, 0);
v_toBind_247_ = lean_ctor_get(v_inst_243_, 1);
lean_inc(v_toBind_247_);
v_toPure_248_ = lean_ctor_get(v_toApplicative_246_, 1);
lean_inc(v_toPure_248_);
v_aliases_249_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_250_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_245_);
v___x_251_ = l_Lean_Syntax_isOfKind(v_stx_245_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v_toBind_247_);
lean_dec(v_stx_245_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
v___x_252_ = lean_apply_2(v_toPure_248_, lean_box(0), v_aliases_249_);
return v___x_252_;
}
else
{
lean_object* v_getCurrNamespace_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_ids_257_; lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v_getCurrNamespace_253_ = lean_ctor_get(v_inst_244_, 0);
lean_inc(v_getCurrNamespace_253_);
lean_dec_ref(v_inst_244_);
lean_inc(v_toPure_248_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_254_, 0, v_toPure_248_);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = l_Lean_Syntax_getArg(v_stx_245_, v___x_255_);
lean_dec(v_stx_245_);
v_ids_257_ = l_Lean_Syntax_getArgs(v___x_256_);
lean_dec(v___x_256_);
v___x_258_ = lean_box(v___x_251_);
lean_inc(v_toBind_247_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_259_, 0, v___x_258_);
lean_closure_set(v___f_259_, 1, v_toPure_248_);
lean_closure_set(v___f_259_, 2, v_ids_257_);
lean_closure_set(v___f_259_, 3, v_inst_243_);
lean_closure_set(v___f_259_, 4, v_aliases_249_);
lean_closure_set(v___f_259_, 5, v_toBind_247_);
lean_closure_set(v___f_259_, 6, v___f_254_);
v___x_260_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v_getCurrNamespace_253_, v___f_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(lean_object* v_m_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_stx_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(v_inst_262_, v_inst_263_, v_stx_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(lean_object* v_k_266_, uint8_t v_defValue_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_scopes_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_opts_274_; lean_object* v_map_275_; lean_object* v___x_276_; 
v___x_270_ = lean_st_ref_get(v___y_268_);
v_scopes_271_ = lean_ctor_get(v___x_270_, 2);
lean_inc(v_scopes_271_);
lean_dec(v___x_270_);
v___x_272_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_273_ = l_List_head_x21___redArg(v___x_272_, v_scopes_271_);
lean_dec(v_scopes_271_);
v_opts_274_ = lean_ctor_get(v___x_273_, 1);
lean_inc_ref(v_opts_274_);
lean_dec(v___x_273_);
v_map_275_ = lean_ctor_get(v_opts_274_, 0);
lean_inc(v_map_275_);
lean_dec_ref(v_opts_274_);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_275_, v_k_266_);
lean_dec(v_map_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_box(v_defValue_267_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v_val_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_292_; 
v_val_279_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_292_ == 0)
{
v___x_281_ = v___x_276_;
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_val_279_);
lean_dec(v___x_276_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_292_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
if (lean_obj_tag(v_val_279_) == 1)
{
uint8_t v_v_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v_v_283_ = lean_ctor_get_uint8(v_val_279_, 0);
lean_dec_ref_known(v_val_279_, 0);
v___x_284_ = lean_box(v_v_283_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 0);
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_290_; 
lean_dec(v_val_279_);
v___x_288_ = lean_box(v_defValue_267_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 0);
lean_ctor_set(v___x_281_, 0, v___x_288_);
v___x_290_ = v___x_281_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg___boxed(lean_object* v_k_293_, lean_object* v_defValue_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v_defValue_boxed_297_; lean_object* v_res_298_; 
v_defValue_boxed_297_ = lean_unbox(v_defValue_294_);
v_res_298_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(v_k_293_, v_defValue_boxed_297_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v_k_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object* v_k_299_, uint8_t v_defValue_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(v_k_299_, v_defValue_300_, v___y_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object* v_k_305_, lean_object* v_defValue_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v_defValue_boxed_310_; lean_object* v_res_311_; 
v_defValue_boxed_310_ = lean_unbox(v_defValue_306_);
v_res_311_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_k_305_, v_defValue_boxed_310_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v_k_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(lean_object* v_as_313_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
v___f_314_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0));
v___x_315_ = l_List_eraseDupsBy___redArg(v___f_314_, v_as_313_);
return v___x_315_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
v___x_318_ = l_Lean_Syntax_isOfKind(v_x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(v_x_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(uint8_t v___x_322_, lean_object* v___x_323_, lean_object* v_as_324_, size_t v_sz_325_, size_t v_i_326_, lean_object* v_b_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v___x_323_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_327_);
return v___x_330_;
}
else
{
lean_object* v_a_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___y_335_; lean_object* v___x_343_; 
v_a_331_ = lean_array_uget_borrowed(v_as_324_, v_i_326_);
v___x_332_ = l_Lean_TSyntax_getId(v_a_331_);
v___x_333_ = 0;
v___x_343_ = l_Lean_Syntax_getRange_x3f(v_a_331_, v___x_333_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_335_ = v___x_344_;
goto v___jp_334_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_343_, 1);
v___y_335_ = v_val_345_;
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; 
v___x_336_ = l_Lean_Syntax_ofRange(v___y_335_, v___x_322_);
lean_inc(v___x_323_);
v___x_337_ = l_Lean_Name_append(v___x_323_, v___x_332_);
v___x_338_ = l_Lean_mkIdentFrom(v___x_336_, v___x_337_, v___x_333_);
lean_dec(v___x_336_);
v___x_339_ = lean_array_push(v_b_327_, v___x_338_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_326_, v___x_340_);
v_i_326_ = v___x_341_;
v_b_327_ = v___x_339_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg___boxed(lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v_as_348_, lean_object* v_sz_349_, lean_object* v_i_350_, lean_object* v_b_351_, lean_object* v___y_352_){
_start:
{
uint8_t v___x_8535__boxed_353_; size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v___x_8535__boxed_353_ = lean_unbox(v___x_346_);
v_sz_boxed_354_ = lean_unbox_usize(v_sz_349_);
lean_dec(v_sz_349_);
v_i_boxed_355_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_8535__boxed_353_, v___x_347_, v_as_348_, v_sz_boxed_354_, v_i_boxed_355_, v_b_351_);
lean_dec_ref(v_as_348_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(lean_object* v_stx_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_aliases_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_aliases_361_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_362_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_357_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_stx_357_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec(v_stx_357_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_aliases_361_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Elab_Command_getScope___redArg(v___y_359_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_currNamespace_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_ids_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v_currNamespace_367_ = lean_ctor_get(v_a_366_, 2);
lean_inc(v_currNamespace_367_);
lean_dec(v_a_366_);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_368_);
lean_dec(v_stx_357_);
v_ids_370_ = l_Lean_Syntax_getArgs(v___x_369_);
lean_dec(v___x_369_);
v_sz_371_ = lean_array_size(v_ids_370_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_363_, v_currNamespace_367_, v_ids_370_, v_sz_371_, v___x_372_, v_aliases_361_);
lean_dec_ref(v_ids_370_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_stx_357_);
v_a_390_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_365_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_365_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10___boxed(lean_object* v_stx_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(v_stx_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_402_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15(lean_object* v_opts_403_, lean_object* v_opt_404_){
_start:
{
lean_object* v_name_405_; lean_object* v_defValue_406_; lean_object* v_map_407_; lean_object* v___x_408_; 
v_name_405_ = lean_ctor_get(v_opt_404_, 0);
v_defValue_406_ = lean_ctor_get(v_opt_404_, 1);
v_map_407_ = lean_ctor_get(v_opts_403_, 0);
v___x_408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_407_, v_name_405_);
if (lean_obj_tag(v___x_408_) == 0)
{
uint8_t v___x_409_; 
v___x_409_ = lean_unbox(v_defValue_406_);
return v___x_409_;
}
else
{
lean_object* v_val_410_; 
v_val_410_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v___x_408_, 1);
if (lean_obj_tag(v_val_410_) == 1)
{
uint8_t v_v_411_; 
v_v_411_ = lean_ctor_get_uint8(v_val_410_, 0);
lean_dec_ref_known(v_val_410_, 0);
return v_v_411_;
}
else
{
uint8_t v___x_412_; 
lean_dec(v_val_410_);
v___x_412_ = lean_unbox(v_defValue_406_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15___boxed(lean_object* v_opts_413_, lean_object* v_opt_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15(v_opts_413_, v_opt_414_);
lean_dec_ref(v_opt_414_);
lean_dec_ref(v_opts_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0(uint8_t v___y_418_, uint8_t v_suppressElabErrors_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 1)
{
lean_object* v_pre_421_; 
v_pre_421_ = lean_ctor_get(v_x_420_, 0);
if (lean_obj_tag(v_pre_421_) == 0)
{
lean_object* v_str_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v_str_422_ = lean_ctor_get(v_x_420_, 1);
v___x_423_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___closed__0));
v___x_424_ = lean_string_dec_eq(v_str_422_, v___x_423_);
if (v___x_424_ == 0)
{
return v___y_418_;
}
else
{
return v_suppressElabErrors_419_;
}
}
else
{
return v___y_418_;
}
}
else
{
return v___y_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___boxed(lean_object* v___y_425_, lean_object* v_suppressElabErrors_426_, lean_object* v_x_427_){
_start:
{
uint8_t v___y_8678__boxed_428_; uint8_t v_suppressElabErrors_boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v___y_8678__boxed_428_ = lean_unbox(v___y_425_);
v_suppressElabErrors_boxed_429_ = lean_unbox(v_suppressElabErrors_426_);
v_res_430_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0(v___y_8678__boxed_428_, v_suppressElabErrors_boxed_429_, v_x_427_);
lean_dec(v_x_427_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
lean_ctor_set(v___x_437_, 4, v___x_435_);
lean_ctor_set(v___x_437_, 5, v___x_435_);
lean_ctor_set(v___x_437_, 6, v___x_435_);
lean_ctor_set(v___x_437_, 7, v___x_435_);
lean_ctor_set(v___x_437_, 8, v___x_435_);
lean_ctor_set(v___x_437_, 9, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(32u);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4(void){
_start:
{
size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = ((size_t)5ULL);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_unsigned_to_nat(32u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___x_445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__3);
v___x_446_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_442_);
lean_ctor_set(v___x_446_, 3, v___x_442_);
lean_ctor_set_usize(v___x_446_, 4, v___x_441_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = lean_box(1);
v___x_448_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__4);
v___x_449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__1);
v___x_450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(lean_object* v_msgData_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v___x_456_; lean_object* v_scopes_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_opts_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_454_ = lean_st_ref_get(v___y_452_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v___x_456_ = lean_st_ref_get(v___y_452_);
v_scopes_457_ = lean_ctor_get(v___x_456_, 2);
lean_inc(v_scopes_457_);
lean_dec(v___x_456_);
v___x_458_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_459_ = l_List_head_x21___redArg(v___x_458_, v_scopes_457_);
lean_dec(v_scopes_457_);
v_opts_460_ = lean_ctor_get(v___x_459_, 1);
lean_inc_ref(v_opts_460_);
lean_dec(v___x_459_);
v___x_461_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__2);
v___x_462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___closed__5);
v___x_463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_463_, 0, v_env_455_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
lean_ctor_set(v___x_463_, 3, v_opts_460_);
v___x_464_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_msgData_451_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg___boxed(lean_object* v_msgData_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(v_msgData_466_, v___y_467_);
lean_dec(v___y_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(lean_object* v_ref_471_, lean_object* v_msgData_472_, uint8_t v_severity_473_, uint8_t v_isSilent_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; uint8_t v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; lean_object* v___y_547_; uint8_t v___y_571_; lean_object* v___y_572_; uint8_t v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; uint8_t v___y_579_; uint8_t v___y_580_; uint8_t v___y_581_; uint8_t v___x_596_; uint8_t v___y_598_; uint8_t v___y_599_; uint8_t v___y_600_; uint8_t v___y_602_; uint8_t v___x_614_; 
v___x_596_ = 2;
v___x_614_ = l_Lean_instBEqMessageSeverity_beq(v_severity_473_, v___x_596_);
if (v___x_614_ == 0)
{
v___y_602_ = v___x_614_;
goto v___jp_601_;
}
else
{
uint8_t v___x_615_; 
lean_inc_ref(v_msgData_472_);
v___x_615_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_472_);
v___y_602_ = v___x_615_;
goto v___jp_601_;
}
v___jp_478_:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Elab_Command_getScope___redArg(v___y_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = l_Lean_Elab_Command_getScope___redArg(v___y_486_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_525_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_525_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_525_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_525_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v_currNamespace_495_; lean_object* v_openDecls_496_; lean_object* v_env_497_; lean_object* v_messages_498_; lean_object* v_scopes_499_; lean_object* v_usedQuotCtxts_500_; lean_object* v_nextMacroScope_501_; lean_object* v_maxRecDepth_502_; lean_object* v_ngen_503_; lean_object* v_auxDeclNGen_504_; lean_object* v_infoState_505_; lean_object* v_traceState_506_; lean_object* v_snapshotTasks_507_; lean_object* v_prevLinterStates_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_524_; 
v___x_494_ = lean_st_ref_take(v___y_486_);
v_currNamespace_495_ = lean_ctor_get(v_a_488_, 2);
lean_inc(v_currNamespace_495_);
lean_dec(v_a_488_);
v_openDecls_496_ = lean_ctor_get(v_a_490_, 3);
lean_inc(v_openDecls_496_);
lean_dec(v_a_490_);
v_env_497_ = lean_ctor_get(v___x_494_, 0);
v_messages_498_ = lean_ctor_get(v___x_494_, 1);
v_scopes_499_ = lean_ctor_get(v___x_494_, 2);
v_usedQuotCtxts_500_ = lean_ctor_get(v___x_494_, 3);
v_nextMacroScope_501_ = lean_ctor_get(v___x_494_, 4);
v_maxRecDepth_502_ = lean_ctor_get(v___x_494_, 5);
v_ngen_503_ = lean_ctor_get(v___x_494_, 6);
v_auxDeclNGen_504_ = lean_ctor_get(v___x_494_, 7);
v_infoState_505_ = lean_ctor_get(v___x_494_, 8);
v_traceState_506_ = lean_ctor_get(v___x_494_, 9);
v_snapshotTasks_507_ = lean_ctor_get(v___x_494_, 10);
v_prevLinterStates_508_ = lean_ctor_get(v___x_494_, 11);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_524_ == 0)
{
v___x_510_ = v___x_494_;
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_prevLinterStates_508_);
lean_inc(v_snapshotTasks_507_);
lean_inc(v_traceState_506_);
lean_inc(v_infoState_505_);
lean_inc(v_auxDeclNGen_504_);
lean_inc(v_ngen_503_);
lean_inc(v_maxRecDepth_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_usedQuotCtxts_500_);
lean_inc(v_scopes_499_);
lean_inc(v_messages_498_);
lean_inc(v_env_497_);
lean_dec(v___x_494_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_currNamespace_495_);
lean_ctor_set(v___x_512_, 1, v_openDecls_496_);
v___x_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___y_484_);
lean_inc_ref(v___y_481_);
lean_inc_ref(v___y_480_);
v___x_514_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_514_, 0, v___y_480_);
lean_ctor_set(v___x_514_, 1, v___y_479_);
lean_ctor_set(v___x_514_, 2, v___y_483_);
lean_ctor_set(v___x_514_, 3, v___y_481_);
lean_ctor_set(v___x_514_, 4, v___x_513_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5, v___y_482_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5 + 1, v___y_485_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5 + 2, v_isSilent_474_);
v___x_515_ = l_Lean_MessageLog_add(v___x_514_, v_messages_498_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_515_);
v___x_517_ = v___x_510_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_env_497_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_scopes_499_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_usedQuotCtxts_500_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_523_, 5, v_maxRecDepth_502_);
lean_ctor_set(v_reuseFailAlloc_523_, 6, v_ngen_503_);
lean_ctor_set(v_reuseFailAlloc_523_, 7, v_auxDeclNGen_504_);
lean_ctor_set(v_reuseFailAlloc_523_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_523_, 9, v_traceState_506_);
lean_ctor_set(v_reuseFailAlloc_523_, 10, v_snapshotTasks_507_);
lean_ctor_set(v_reuseFailAlloc_523_, 11, v_prevLinterStates_508_);
v___x_517_ = v_reuseFailAlloc_523_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = lean_st_ref_set(v___y_486_, v___x_517_);
v___x_519_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_519_);
v___x_521_ = v___x_492_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_488_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_479_);
v_a_526_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_489_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_489_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_479_);
v_a_534_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_487_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_487_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
v___jp_542_:
{
lean_object* v_fileName_548_; lean_object* v_fileMap_549_; uint8_t v_suppressElabErrors_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_569_; 
v_fileName_548_ = lean_ctor_get(v___y_475_, 0);
v_fileMap_549_ = lean_ctor_get(v___y_475_, 1);
v_suppressElabErrors_550_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*10);
v___x_551_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_472_);
v___x_552_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(v___x_551_, v___y_476_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_569_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc_ref_n(v_fileMap_549_, 2);
v___x_557_ = l_Lean_FileMap_toPosition(v_fileMap_549_, v___y_545_);
lean_dec(v___y_545_);
v___x_558_ = l_Lean_FileMap_toPosition(v_fileMap_549_, v___y_547_);
lean_dec(v___y_547_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___closed__0));
if (v_suppressElabErrors_550_ == 0)
{
lean_del_object(v___x_555_);
v___y_479_ = v___x_557_;
v___y_480_ = v_fileName_548_;
v___y_481_ = v___x_560_;
v___y_482_ = v___y_544_;
v___y_483_ = v___x_559_;
v___y_484_ = v_a_553_;
v___y_485_ = v___y_546_;
v___y_486_ = v___y_476_;
goto v___jp_478_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___f_563_; uint8_t v___x_564_; 
v___x_561_ = lean_box(v___y_543_);
v___x_562_ = lean_box(v_suppressElabErrors_550_);
v___f_563_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_563_, 0, v___x_561_);
lean_closure_set(v___f_563_, 1, v___x_562_);
lean_inc(v_a_553_);
v___x_564_ = l_Lean_MessageData_hasTag(v___f_563_, v_a_553_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec_ref_known(v___x_559_, 1);
lean_dec_ref(v___x_557_);
lean_dec(v_a_553_);
v___x_565_ = lean_box(0);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_565_);
v___x_567_ = v___x_555_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_del_object(v___x_555_);
v___y_479_ = v___x_557_;
v___y_480_ = v_fileName_548_;
v___y_481_ = v___x_560_;
v___y_482_ = v___y_544_;
v___y_483_ = v___x_559_;
v___y_484_ = v_a_553_;
v___y_485_ = v___y_546_;
v___y_486_ = v___y_476_;
goto v___jp_478_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Syntax_getTailPos_x3f(v___y_572_, v___y_573_);
lean_dec(v___y_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_inc(v___y_575_);
v___y_543_ = v___y_571_;
v___y_544_ = v___y_573_;
v___y_545_ = v___y_575_;
v___y_546_ = v___y_574_;
v___y_547_ = v___y_575_;
goto v___jp_542_;
}
else
{
lean_object* v_val_577_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_576_, 1);
v___y_543_ = v___y_571_;
v___y_544_ = v___y_573_;
v___y_545_ = v___y_575_;
v___y_546_ = v___y_574_;
v___y_547_ = v_val_577_;
goto v___jp_542_;
}
}
v___jp_578_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_Command_getRef___redArg(v___y_475_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v_ref_584_; lean_object* v___x_585_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v_ref_584_ = l_Lean_replaceRef(v_ref_471_, v_a_583_);
lean_dec(v_a_583_);
v___x_585_ = l_Lean_Syntax_getPos_x3f(v_ref_584_, v___y_580_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___y_571_ = v___y_579_;
v___y_572_ = v_ref_584_;
v___y_573_ = v___y_580_;
v___y_574_ = v___y_581_;
v___y_575_ = v___x_586_;
goto v___jp_570_;
}
else
{
lean_object* v_val_587_; 
v_val_587_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_585_, 1);
v___y_571_ = v___y_579_;
v___y_572_ = v_ref_584_;
v___y_573_ = v___y_580_;
v___y_574_ = v___y_581_;
v___y_575_ = v_val_587_;
goto v___jp_570_;
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_msgData_472_);
v_a_588_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_582_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_582_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
v___jp_597_:
{
if (v___y_600_ == 0)
{
v___y_579_ = v___y_598_;
v___y_580_ = v___y_599_;
v___y_581_ = v_severity_473_;
goto v___jp_578_;
}
else
{
v___y_579_ = v___y_598_;
v___y_580_ = v___y_599_;
v___y_581_ = v___x_596_;
goto v___jp_578_;
}
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_scopes_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_opts_607_; uint8_t v___x_608_; uint8_t v___x_609_; 
v___x_603_ = lean_st_ref_get(v___y_476_);
v_scopes_604_ = lean_ctor_get(v___x_603_, 2);
lean_inc(v_scopes_604_);
lean_dec(v___x_603_);
v___x_605_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_606_ = l_List_head_x21___redArg(v___x_605_, v_scopes_604_);
lean_dec(v_scopes_604_);
v_opts_607_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_opts_607_);
lean_dec(v___x_606_);
v___x_608_ = 1;
v___x_609_ = l_Lean_instBEqMessageSeverity_beq(v_severity_473_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_opts_607_);
v___y_598_ = v___y_602_;
v___y_599_ = v___y_602_;
v___y_600_ = v___x_609_;
goto v___jp_597_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = l_Lean_warningAsError;
v___x_611_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15(v_opts_607_, v___x_610_);
lean_dec_ref(v_opts_607_);
v___y_598_ = v___y_602_;
v___y_599_ = v___y_602_;
v___y_600_ = v___x_611_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_msgData_472_);
v___x_612_ = lean_box(0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___boxed(lean_object* v_ref_616_, lean_object* v_msgData_617_, lean_object* v_severity_618_, lean_object* v_isSilent_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v_severity_boxed_623_; uint8_t v_isSilent_boxed_624_; lean_object* v_res_625_; 
v_severity_boxed_623_ = lean_unbox(v_severity_618_);
v_isSilent_boxed_624_ = lean_unbox(v_isSilent_619_);
v_res_625_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(v_ref_616_, v_msgData_617_, v_severity_boxed_623_, v_isSilent_boxed_624_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v_ref_616_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(lean_object* v_ref_626_, lean_object* v_msgData_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; 
v___x_631_ = 1;
v___x_632_ = 0;
v___x_633_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(v_ref_626_, v_msgData_627_, v___x_631_, v___x_632_, v___y_628_, v___y_629_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(lean_object* v_ref_634_, lean_object* v_msgData_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_ref_634_, v_msgData_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v_ref_634_);
return v_res_639_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__0));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__2));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object* v_linterOption_646_, lean_object* v_stx_647_, lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_name_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_670_; 
v_name_652_ = lean_ctor_get(v_linterOption_646_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_linterOption_646_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_linterOption_646_, 1);
lean_dec(v_unused_671_);
v___x_654_ = v_linterOption_646_;
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_name_652_);
lean_dec(v_linterOption_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1);
lean_inc(v_name_652_);
v___x_657_ = l_Lean_MessageData_ofName(v_name_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 7);
lean_ctor_set(v___x_654_, 1, v___x_657_);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_669_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_disable_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_660_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v_disable_662_ = l_Lean_MessageData_note(v___x_661_);
v___x_663_ = l_Lean_Linter_linterMessageTag;
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v_msg_648_);
lean_ctor_set(v___x_664_, 1, v_disable_662_);
v___x_665_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_666_, 0, v_name_652_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v_stx_647_);
v___x_667_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_667_, 0, v_stx_647_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_stx_647_, v___x_667_, v___y_649_, v___y_650_);
lean_dec(v_stx_647_);
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object* v_linterOption_672_, lean_object* v_stx_673_, lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_linterOption_672_, v_stx_673_, v_msg_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
if (lean_obj_tag(v_a_679_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_array_to_list(v_a_680_);
return v___x_681_;
}
else
{
lean_object* v_head_682_; lean_object* v_tail_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; uint8_t v___x_686_; 
v_head_682_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_head_682_);
v_tail_683_ = lean_ctor_get(v_a_679_, 1);
lean_inc(v_tail_683_);
lean_dec_ref_known(v_a_679_, 2);
v_fst_684_ = lean_ctor_get(v_head_682_, 0);
lean_inc(v_fst_684_);
v_snd_685_ = lean_ctor_get(v_head_682_, 1);
lean_inc(v_snd_685_);
lean_dec(v_head_682_);
v___x_686_ = lean_name_eq(v_fst_684_, v_snd_685_);
lean_dec(v_snd_685_);
if (v___x_686_ == 0)
{
lean_dec(v_fst_684_);
v_a_679_ = v_tail_683_;
goto _start;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_array_push(v_a_680_, v_fst_684_);
v_a_679_ = v_tail_683_;
v_a_680_ = v___x_688_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object* v_comp_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
if (lean_obj_tag(v_a_691_) == 0)
{
return v_a_692_;
}
else
{
lean_object* v_head_693_; lean_object* v_tail_694_; uint8_t v___x_695_; 
v_head_693_ = lean_ctor_get(v_a_691_, 0);
v_tail_694_ = lean_ctor_get(v_a_691_, 1);
v___x_695_ = lean_name_eq(v_head_693_, v_comp_690_);
if (v___x_695_ == 0)
{
v_a_691_ = v_tail_694_;
goto _start;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_a_692_, v___x_697_);
lean_dec(v_a_692_);
v_a_691_ = v_tail_694_;
v_a_692_ = v___x_698_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6___boxed(lean_object* v_comp_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v_comp_700_, v_a_701_, v_a_702_);
lean_dec(v_a_701_);
lean_dec(v_comp_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object* v___x_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
if (lean_obj_tag(v_a_705_) == 0)
{
lean_object* v___x_707_; 
v___x_707_ = l_List_reverse___redArg(v_a_706_);
return v___x_707_;
}
else
{
lean_object* v_head_708_; lean_object* v_tail_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_722_; 
v_head_708_ = lean_ctor_get(v_a_705_, 0);
v_tail_709_ = lean_ctor_get(v_a_705_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_722_ == 0)
{
v___x_711_ = v_a_705_;
v_isShared_712_ = v_isSharedCheck_722_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_tail_709_);
lean_inc(v_head_708_);
lean_dec(v_a_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_722_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v_head_708_, v___x_704_, v___x_714_);
v___x_716_ = lean_nat_dec_lt(v___x_713_, v___x_715_);
lean_dec(v___x_715_);
if (v___x_716_ == 0)
{
lean_del_object(v___x_711_);
lean_dec(v_head_708_);
v_a_705_ = v_tail_709_;
goto _start;
}
else
{
lean_object* v___x_719_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_a_706_);
v___x_719_ = v___x_711_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_head_708_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_a_706_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v_a_705_ = v_tail_709_;
v_a_706_ = v___x_719_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object* v___x_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_723_, v_a_724_, v_a_725_);
lean_dec(v___x_723_);
return v_res_726_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0));
v___x_729_ = l_Lean_stringToMessageData(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
if (lean_obj_tag(v_a_730_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = l_List_reverse___redArg(v_a_731_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v_tail_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_746_; 
v_head_733_ = lean_ctor_get(v_a_730_, 0);
v_tail_734_ = lean_ctor_get(v_a_730_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_730_);
if (v_isSharedCheck_746_ == 0)
{
v___x_736_ = v_a_730_;
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_tail_734_);
lean_inc(v_head_733_);
lean_dec(v_a_730_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_738_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
v___x_739_ = l_Lean_MessageData_ofName(v_head_733_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_738_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_a_731_);
lean_ctor_set(v___x_736_, 0, v___x_741_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_731_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v_a_730_ = v_tail_734_;
v_a_731_ = v___x_743_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6));
v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(uint8_t v___x_764_, lean_object* v_as_765_, size_t v_sz_766_, size_t v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_a_773_; uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_lt(v_i_767_, v_sz_766_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_b_768_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = lean_box(0);
v_a_780_ = lean_array_uget_borrowed(v_as_765_, v_i_767_);
v___x_781_ = l_Lean_Syntax_getId(v_a_780_);
v___x_782_ = l_Lean_Name_hasMacroScopes(v___x_781_);
if (v___x_782_ == 0)
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_isPrivateName(v___x_781_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_785_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(v___x_784_, v___x_764_, v___y_770_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v___y_789_; lean_object* v___x_821_; lean_object* v___y_823_; uint8_t v___x_827_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
lean_inc(v___x_781_);
v___x_821_ = l_Lean_Name_components(v___x_781_);
v___x_827_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
lean_inc(v___x_821_);
v___x_829_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_821_, v___x_821_, v___x_828_);
lean_dec(v___x_821_);
v___x_830_ = l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(v___x_829_);
v___y_789_ = v___x_830_;
goto v___jp_788_;
}
else
{
if (lean_obj_tag(v___x_821_) == 0)
{
v___y_823_ = v___x_821_;
goto v___jp_822_;
}
else
{
lean_object* v_tail_831_; 
v_tail_831_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_tail_831_);
v___y_823_ = v_tail_831_;
goto v___jp_822_;
}
}
v___jp_788_:
{
if (lean_obj_tag(v___y_789_) == 0)
{
lean_dec(v___x_781_);
v_a_773_ = v___x_779_;
goto v___jp_772_;
}
else
{
lean_object* v_tail_790_; 
v_tail_790_ = lean_ctor_get(v___y_789_, 1);
if (lean_obj_tag(v_tail_790_) == 0)
{
lean_object* v_head_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_807_; 
v_head_791_ = lean_ctor_get(v___y_789_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___y_789_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___y_789_, 1);
lean_dec(v_unused_808_);
v___x_793_ = v___y_789_;
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_head_791_);
lean_dec(v___y_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_807_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1);
v___x_796_ = l_Lean_MessageData_ofName(v_head_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 7);
lean_ctor_set(v___x_793_, 1, v___x_796_);
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_798_ = v___x_793_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_806_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_MessageData_ofConstName(v___x_781_, v___x_764_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
lean_inc(v_a_780_);
v___x_805_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_787_, v_a_780_, v___x_804_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_dec_ref_known(v___x_805_, 1);
v_a_773_ = v___x_779_;
goto v___jp_772_;
}
else
{
return v___x_805_;
}
}
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_809_ = lean_box(0);
v___x_810_ = l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___y_789_, v___x_809_);
v___x_811_ = l_Lean_MessageData_andList(v___x_810_);
v___x_812_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
v___x_814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofConstName(v___x_781_, v___x_764_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
lean_inc(v_a_780_);
v___x_820_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_787_, v_a_780_, v___x_819_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref_known(v___x_820_, 1);
v_a_773_ = v___x_779_;
goto v___jp_772_;
}
else
{
return v___x_820_;
}
}
}
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v___x_821_, v___y_823_);
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10));
v___x_826_ = l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v___x_824_, v___x_825_);
v___y_789_ = v___x_826_;
goto v___jp_788_;
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v___x_781_);
v_a_832_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_785_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_785_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_dec(v___x_781_);
v_a_773_ = v___x_779_;
goto v___jp_772_;
}
}
else
{
lean_dec(v___x_781_);
v_a_773_ = v___x_779_;
goto v___jp_772_;
}
}
v___jp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_767_, v___x_774_);
v_i_767_ = v___x_775_;
v_b_768_ = v_a_773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___boxed(lean_object* v___x_840_, lean_object* v_as_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v___x_9295__boxed_848_; size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v___x_9295__boxed_848_ = lean_unbox(v___x_840_);
v_sz_boxed_849_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_850_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_9295__boxed_848_, v_as_841_, v_sz_boxed_849_, v_i_boxed_850_, v_b_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec_ref(v_as_841_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object* v___x_852_, lean_object* v_pos_853_, lean_object* v_init_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_d_858_; 
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v_k_861_; lean_object* v_v_862_; lean_object* v_l_863_; lean_object* v_r_864_; lean_object* v___x_865_; lean_object* v_a_866_; 
v_k_861_ = lean_ctor_get(v_x_855_, 1);
lean_inc(v_k_861_);
v_v_862_ = lean_ctor_get(v_x_855_, 2);
lean_inc(v_v_862_);
v_l_863_ = lean_ctor_get(v_x_855_, 3);
lean_inc(v_l_863_);
v_r_864_ = lean_ctor_get(v_x_855_, 4);
lean_inc(v_r_864_);
lean_dec_ref_known(v_x_855_, 5);
v___x_865_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_852_, v_pos_853_, v_init_854_, v_l_863_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
if (lean_obj_tag(v_a_866_) == 0)
{
lean_object* v_a_867_; 
lean_dec_ref(v___x_865_);
lean_dec(v_r_864_);
lean_dec(v_v_862_);
lean_dec(v_k_861_);
v_a_867_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v_a_866_, 1);
v_d_858_ = v_a_867_;
goto v___jp_857_;
}
else
{
lean_object* v_range_868_; lean_object* v_a_869_; lean_object* v_selectionRange_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_893_; 
v_range_868_ = lean_ctor_get(v_v_862_, 0);
lean_inc_ref(v_range_868_);
v_a_869_ = lean_ctor_get(v_a_866_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v_a_866_, 1);
v_selectionRange_870_ = lean_ctor_get(v_v_862_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_v_862_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_v_862_, 0);
lean_dec(v_unused_894_);
v___x_872_ = v_v_862_;
v_isShared_873_ = v_isSharedCheck_893_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_selectionRange_870_);
lean_dec(v_v_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_893_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_pos_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_pos_874_ = lean_ctor_get(v_range_868_, 0);
lean_inc_ref(v_pos_874_);
lean_dec_ref(v_range_868_);
v___x_875_ = l_Lean_FileMap_ofPosition(v___x_852_, v_pos_874_);
v___x_876_ = lean_nat_dec_le(v_pos_853_, v___x_875_);
lean_dec(v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v_a_877_; 
lean_del_object(v___x_872_);
lean_dec_ref(v_selectionRange_870_);
lean_dec(v_a_869_);
lean_dec(v_k_861_);
v_a_877_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v___x_865_);
if (lean_obj_tag(v_a_877_) == 0)
{
lean_object* v_a_878_; 
lean_dec(v_r_864_);
v_a_878_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_a_877_, 1);
v_d_858_ = v_a_878_;
goto v___jp_857_;
}
else
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v_a_877_, 1);
v_init_854_ = v_a_879_;
v_x_855_ = v_r_864_;
goto _start;
}
}
else
{
lean_object* v_pos_881_; lean_object* v_endPos_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec_ref(v___x_865_);
v_pos_881_ = lean_ctor_get(v_selectionRange_870_, 0);
lean_inc_ref(v_pos_881_);
v_endPos_882_ = lean_ctor_get(v_selectionRange_870_, 2);
lean_inc_ref(v_endPos_882_);
lean_dec_ref(v_selectionRange_870_);
v___x_883_ = l_Lean_FileMap_ofPosition(v___x_852_, v_pos_881_);
v___x_884_ = l_Lean_FileMap_ofPosition(v___x_852_, v_endPos_882_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_884_);
lean_ctor_set(v___x_872_, 0, v___x_883_);
v___x_886_ = v___x_872_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_892_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Lean_Syntax_ofRange(v___x_886_, v___x_876_);
v___x_888_ = 0;
v___x_889_ = l_Lean_mkIdentFrom(v___x_887_, v_k_861_, v___x_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_array_push(v_a_869_, v___x_889_);
v_init_854_ = v___x_890_;
v_x_855_ = v_r_864_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_init_854_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v_d_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object* v___x_897_, lean_object* v_pos_898_, lean_object* v_init_899_, lean_object* v_x_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_897_, v_pos_898_, v_init_899_, v_x_900_);
lean_dec(v_pos_898_);
lean_dec_ref(v___x_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object* v_pos_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_env_908_; lean_object* v_fileMap_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_drs_914_; lean_object* v_nms_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v___x_907_ = lean_st_ref_get(v___y_905_);
v_env_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_907_);
v_fileMap_909_ = lean_ctor_get(v___y_904_, 1);
v___x_910_ = lean_box(1);
v___x_911_ = l_Lean_declRangeExt;
v___x_912_ = lean_box(1);
v___x_913_ = lean_box(0);
v_drs_914_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_910_, v___x_911_, v_env_908_, v___x_912_, v___x_913_);
v_nms_915_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_916_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_909_, v_pos_903_, v_nms_915_, v_drs_914_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_a_921_; lean_object* v___x_923_; 
v_a_921_ = lean_ctor_get(v_a_917_, 0);
lean_inc(v_a_921_);
lean_dec(v_a_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_a_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object* v_pos_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v_pos_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_pos_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object* v_o_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; lean_object* v_env_935_; lean_object* v___x_936_; lean_object* v_toEnvExtension_937_; lean_object* v_asyncMode_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_merged_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_950_; 
v___x_934_ = lean_st_ref_get(v___y_932_);
v_env_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc_ref(v_env_935_);
lean_dec(v___x_934_);
v___x_936_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_937_ = lean_ctor_get(v___x_936_, 0);
v_asyncMode_938_ = lean_ctor_get(v_toEnvExtension_937_, 2);
v___x_939_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_940_ = lean_box(0);
v___x_941_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_939_, v___x_936_, v_env_935_, v_asyncMode_938_, v___x_940_);
v_merged_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_941_, 1);
lean_dec(v_unused_951_);
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_merged_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_merged_942_);
lean_ctor_set(v___x_944_, 0, v_o_931_);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_o_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_merged_942_);
v___x_947_ = v_reuseFailAlloc_949_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object* v_o_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_952_, v___y_953_);
lean_dec(v___y_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_scopes_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_opts_963_; lean_object* v___x_964_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_scopes_960_ = lean_ctor_get(v___x_959_, 2);
lean_inc(v_scopes_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_962_ = l_List_head_x21___redArg(v___x_961_, v_scopes_960_);
lean_dec(v_scopes_960_);
v_opts_963_ = lean_ctor_get(v___x_962_, 1);
lean_inc_ref(v_opts_963_);
lean_dec(v___x_962_);
v___x_964_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_opts_963_, v___y_957_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(lean_object* v___f_969_, lean_object* v_stx_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1034_; 
v___x_974_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_971_, v___y_972_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1034_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1034_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v_aliases_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; 
v___x_979_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
v___x_980_ = l_Lean_Linter_getLinterValue(v___x_979_, v_a_975_);
lean_dec(v_a_975_);
if (v___x_980_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v_stx_970_);
lean_dec_ref(v___f_969_);
v___x_1017_ = lean_box(0);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_1017_);
v___x_1019_ = v___x_977_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1021_; 
lean_del_object(v___x_977_);
lean_inc(v_stx_970_);
v___x_1021_ = l_Lean_Syntax_find_x3f(v_stx_970_, v___f_969_);
if (lean_obj_tag(v___x_1021_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1023_; 
v_val_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(v_val_1022_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_aliases_1010_ = v_a_1024_;
v___y_1011_ = v___y_971_;
v___y_1012_ = v___y_972_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_stx_970_);
v_a_1025_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1033_; 
lean_dec(v___x_1021_);
v___x_1033_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v_aliases_1010_ = v___x_1033_;
v___y_1011_ = v___y_971_;
v___y_1012_ = v___y_972_;
goto v___jp_1009_;
}
}
v___jp_981_:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v___y_985_, v___y_982_, v___y_983_);
lean_dec(v___y_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; size_t v_sz_990_; size_t v___x_991_; lean_object* v___x_992_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Array_append___redArg(v_a_987_, v___y_984_);
lean_dec_ref(v___y_984_);
v___x_989_ = lean_box(0);
v_sz_990_ = lean_array_size(v___x_988_);
v___x_991_ = ((size_t)0ULL);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_980_, v___x_988_, v_sz_990_, v___x_991_, v___x_989_, v___y_982_, v___y_983_);
lean_dec_ref(v___x_988_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1000_);
v___x_994_ = v___x_992_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_dec(v___x_992_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_989_);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_989_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
return v___x_992_;
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v___y_984_);
v_a_1001_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_986_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_986_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
v___jp_1009_:
{
uint8_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = 0;
v___x_1014_ = l_Lean_Syntax_getPos_x3f(v_stx_970_, v___x_1013_);
lean_dec(v_stx_970_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v___y_982_ = v___y_1011_;
v___y_983_ = v___y_1012_;
v___y_984_ = v_aliases_1010_;
v___y_985_ = v___x_1015_;
goto v___jp_981_;
}
else
{
lean_object* v_val_1016_; 
v_val_1016_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1014_, 1);
v___y_982_ = v___y_1011_;
v___y_983_ = v___y_1012_;
v___y_984_ = v_aliases_1010_;
v___y_985_ = v_val_1016_;
goto v___jp_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(lean_object* v___f_1035_, lean_object* v_stx_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(v___f_1035_, v_stx_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object* v_o_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_1057_, v___y_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object* v_o_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(v_o_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object* v___x_1067_, lean_object* v_pos_1068_, lean_object* v_init_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1067_, v_pos_1068_, v_init_1069_, v_x_1070_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object* v___x_1075_, lean_object* v_pos_1076_, lean_object* v_init_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(v___x_1075_, v_pos_1076_, v_init_1077_, v_x_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_pos_1076_);
lean_dec_ref(v___x_1075_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(uint8_t v___x_1083_, lean_object* v___x_1084_, lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_1083_, v___x_1084_, v_as_1085_, v_sz_1086_, v_i_1087_, v_b_1088_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___boxed(lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v_as_1095_, lean_object* v_sz_1096_, lean_object* v_i_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_9853__boxed_1102_; size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v___x_9853__boxed_1102_ = lean_unbox(v___x_1093_);
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1096_);
lean_dec(v_sz_1096_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1097_);
lean_dec(v_i_1097_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(v___x_9853__boxed_1102_, v___x_1094_, v_as_1095_, v_sz_boxed_1103_, v_i_boxed_1104_, v_b_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_as_1095_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14(lean_object* v_msgData_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(v_msgData_1106_, v___y_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___boxed(lean_object* v_msgData_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14(v_msgData_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace));
v___x_1118_ = l_Lean_Elab_Command_addLinter(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
return v_res_1120_;
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
res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_2308209999____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_dupNamespace = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_dupNamespace);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_dupNamespace_consecutiveOnly = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_dupNamespace_consecutiveOnly);
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
