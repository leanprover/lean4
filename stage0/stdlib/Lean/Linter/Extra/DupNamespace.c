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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___closed__1_value)} };
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
uint8_t v___x_215__boxed_209_; lean_object* v_res_210_; 
v___x_215__boxed_209_ = lean_unbox(v___x_203_);
v_res_210_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(v___x_215__boxed_209_, v_currNamespace_204_, v_toPure_205_, v_a_206_, v_x_207_, v___y_208_);
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
uint8_t v___x_250__boxed_233_; lean_object* v_res_234_; 
v___x_250__boxed_233_ = lean_unbox(v___x_225_);
v_res_234_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(v___x_250__boxed_233_, v_toPure_226_, v_ids_227_, v_inst_228_, v_aliases_229_, v_toBind_230_, v___f_231_, v_currNamespace_232_);
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
uint8_t v___x_7706__boxed_353_; size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v___x_7706__boxed_353_ = lean_unbox(v___x_346_);
v_sz_boxed_354_ = lean_unbox_usize(v_sz_349_);
lean_dec(v_sz_349_);
v_i_boxed_355_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_7706__boxed_353_, v___x_347_, v_as_348_, v_sz_boxed_354_, v_i_boxed_355_, v_b_351_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0(uint8_t v_suppressElabErrors_418_, uint8_t v___y_419_, lean_object* v_x_420_){
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
return v___x_424_;
}
else
{
return v_suppressElabErrors_418_;
}
}
else
{
return v___y_419_;
}
}
else
{
return v___y_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_425_, lean_object* v___y_426_, lean_object* v_x_427_){
_start:
{
uint8_t v_suppressElabErrors_boxed_428_; uint8_t v___y_7849__boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_suppressElabErrors_boxed_428_ = lean_unbox(v_suppressElabErrors_425_);
v___y_7849__boxed_429_ = lean_unbox(v___y_426_);
v_res_430_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0(v_suppressElabErrors_boxed_428_, v___y_7849__boxed_429_, v_x_427_);
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
v___x_437_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_437_, 10, v___x_435_);
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
lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; uint8_t v___y_547_; lean_object* v___y_548_; uint8_t v___y_572_; lean_object* v___y_573_; uint8_t v___y_574_; uint8_t v___y_575_; lean_object* v___y_576_; uint8_t v___y_580_; uint8_t v___y_581_; uint8_t v___y_582_; uint8_t v___x_597_; uint8_t v___y_599_; uint8_t v___y_600_; uint8_t v___y_601_; uint8_t v___y_603_; uint8_t v___x_615_; 
v___x_597_ = 2;
v___x_615_ = l_Lean_instBEqMessageSeverity_beq(v_severity_473_, v___x_597_);
if (v___x_615_ == 0)
{
v___y_603_ = v___x_615_;
goto v___jp_602_;
}
else
{
uint8_t v___x_616_; 
lean_inc_ref(v_msgData_472_);
v___x_616_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_472_);
v___y_603_ = v___x_616_;
goto v___jp_602_;
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
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_526_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_526_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_526_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_526_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v_currNamespace_495_; lean_object* v_openDecls_496_; lean_object* v_env_497_; lean_object* v_messages_498_; lean_object* v_scopes_499_; lean_object* v_usedQuotCtxts_500_; lean_object* v_nextMacroScope_501_; lean_object* v_maxRecDepth_502_; lean_object* v_ngen_503_; lean_object* v_auxDeclNGen_504_; lean_object* v_infoState_505_; lean_object* v_traceState_506_; lean_object* v_snapshotTasks_507_; lean_object* v_prevLinterStates_508_; lean_object* v_codeQualityEntryTasks_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_525_; 
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
v_codeQualityEntryTasks_509_ = lean_ctor_get(v___x_494_, 12);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_525_ == 0)
{
v___x_511_ = v___x_494_;
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_codeQualityEntryTasks_509_);
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
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_currNamespace_495_);
lean_ctor_set(v___x_513_, 1, v_openDecls_496_);
v___x_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_482_);
v___x_515_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_515_, 0, v___y_482_);
lean_ctor_set(v___x_515_, 1, v___y_483_);
lean_ctor_set(v___x_515_, 2, v___y_481_);
lean_ctor_set(v___x_515_, 3, v___y_479_);
lean_ctor_set(v___x_515_, 4, v___x_514_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*5, v___y_485_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*5 + 1, v___y_484_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*5 + 2, v_isSilent_474_);
v___x_516_ = l_Lean_MessageLog_add(v___x_515_, v_messages_498_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_516_);
v___x_518_ = v___x_511_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_env_497_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_scopes_499_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_usedQuotCtxts_500_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_524_, 5, v_maxRecDepth_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 6, v_ngen_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 7, v_auxDeclNGen_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_524_, 9, v_traceState_506_);
lean_ctor_set(v_reuseFailAlloc_524_, 10, v_snapshotTasks_507_);
lean_ctor_set(v_reuseFailAlloc_524_, 11, v_prevLinterStates_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 12, v_codeQualityEntryTasks_509_);
v___x_518_ = v_reuseFailAlloc_524_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_st_ref_put(v___y_486_, v___x_518_);
v___x_520_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_520_);
v___x_522_ = v___x_492_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_488_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
v_a_527_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_489_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_489_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v___y_483_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
v_a_535_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_487_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_487_);
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
v___jp_543_:
{
lean_object* v_fileName_549_; lean_object* v_fileMap_550_; uint8_t v_suppressElabErrors_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_570_; 
v_fileName_549_ = lean_ctor_get(v___y_475_, 0);
v_fileMap_550_ = lean_ctor_get(v___y_475_, 1);
v_suppressElabErrors_551_ = lean_ctor_get_uint8(v___y_475_, sizeof(void*)*10);
v___x_552_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_472_);
v___x_553_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(v___x_552_, v___y_476_);
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_570_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_inc_ref_n(v_fileMap_550_, 2);
v___x_558_ = l_Lean_FileMap_toPosition(v_fileMap_550_, v___y_545_);
lean_dec(v___y_545_);
v___x_559_ = l_Lean_FileMap_toPosition(v_fileMap_550_, v___y_548_);
lean_dec(v___y_548_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___closed__0));
if (v_suppressElabErrors_551_ == 0)
{
lean_del_object(v___x_556_);
v___y_479_ = v___x_561_;
v___y_480_ = v_a_554_;
v___y_481_ = v___x_560_;
v___y_482_ = v_fileName_549_;
v___y_483_ = v___x_558_;
v___y_484_ = v___y_546_;
v___y_485_ = v___y_547_;
v___y_486_ = v___y_476_;
goto v___jp_478_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___f_564_; uint8_t v___x_565_; 
v___x_562_ = lean_box(v_suppressElabErrors_551_);
v___x_563_ = lean_box(v___y_544_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_564_, 0, v___x_562_);
lean_closure_set(v___f_564_, 1, v___x_563_);
lean_inc(v_a_554_);
v___x_565_ = l_Lean_MessageData_hasTag(v___f_564_, v_a_554_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec_ref_known(v___x_560_, 1);
lean_dec_ref(v___x_558_);
lean_dec(v_a_554_);
v___x_566_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_566_);
v___x_568_ = v___x_556_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_del_object(v___x_556_);
v___y_479_ = v___x_561_;
v___y_480_ = v_a_554_;
v___y_481_ = v___x_560_;
v___y_482_ = v_fileName_549_;
v___y_483_ = v___x_558_;
v___y_484_ = v___y_546_;
v___y_485_ = v___y_547_;
v___y_486_ = v___y_476_;
goto v___jp_478_;
}
}
}
}
v___jp_571_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Syntax_getTailPos_x3f(v___y_573_, v___y_575_);
lean_dec(v___y_573_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_inc(v___y_576_);
v___y_544_ = v___y_572_;
v___y_545_ = v___y_576_;
v___y_546_ = v___y_574_;
v___y_547_ = v___y_575_;
v___y_548_ = v___y_576_;
goto v___jp_543_;
}
else
{
lean_object* v_val_578_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_577_, 1);
v___y_544_ = v___y_572_;
v___y_545_ = v___y_576_;
v___y_546_ = v___y_574_;
v___y_547_ = v___y_575_;
v___y_548_ = v_val_578_;
goto v___jp_543_;
}
}
v___jp_579_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Elab_Command_getRef___redArg(v___y_475_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_ref_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v_ref_585_ = l_Lean_replaceRef(v_ref_471_, v_a_584_);
lean_dec(v_a_584_);
v___x_586_ = l_Lean_Syntax_getPos_x3f(v_ref_585_, v___y_581_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___y_572_ = v___y_580_;
v___y_573_ = v_ref_585_;
v___y_574_ = v___y_582_;
v___y_575_ = v___y_581_;
v___y_576_ = v___x_587_;
goto v___jp_571_;
}
else
{
lean_object* v_val_588_; 
v_val_588_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v___x_586_, 1);
v___y_572_ = v___y_580_;
v___y_573_ = v_ref_585_;
v___y_574_ = v___y_582_;
v___y_575_ = v___y_581_;
v___y_576_ = v_val_588_;
goto v___jp_571_;
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_msgData_472_);
v_a_589_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_583_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_583_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
v___jp_598_:
{
if (v___y_601_ == 0)
{
v___y_580_ = v___y_599_;
v___y_581_ = v___y_600_;
v___y_582_ = v_severity_473_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___y_599_;
v___y_581_ = v___y_600_;
v___y_582_ = v___x_597_;
goto v___jp_579_;
}
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
lean_object* v___x_604_; lean_object* v_scopes_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_opts_608_; uint8_t v___x_609_; uint8_t v___x_610_; 
v___x_604_ = lean_st_ref_get(v___y_476_);
v_scopes_605_ = lean_ctor_get(v___x_604_, 2);
lean_inc(v_scopes_605_);
lean_dec(v___x_604_);
v___x_606_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_607_ = l_List_head_x21___redArg(v___x_606_, v_scopes_605_);
lean_dec(v_scopes_605_);
v_opts_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc_ref(v_opts_608_);
lean_dec(v___x_607_);
v___x_609_ = 1;
v___x_610_ = l_Lean_instBEqMessageSeverity_beq(v_severity_473_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v_opts_608_);
v___y_599_ = v___y_603_;
v___y_600_ = v___y_603_;
v___y_601_ = v___x_610_;
goto v___jp_598_;
}
else
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = l_Lean_warningAsError;
v___x_612_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__15(v_opts_608_, v___x_611_);
lean_dec_ref(v_opts_608_);
v___y_599_ = v___y_603_;
v___y_600_ = v___y_603_;
v___y_601_ = v___x_612_;
goto v___jp_598_;
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec_ref(v_msgData_472_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7___boxed(lean_object* v_ref_617_, lean_object* v_msgData_618_, lean_object* v_severity_619_, lean_object* v_isSilent_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_severity_boxed_624_; uint8_t v_isSilent_boxed_625_; lean_object* v_res_626_; 
v_severity_boxed_624_ = lean_unbox(v_severity_619_);
v_isSilent_boxed_625_ = lean_unbox(v_isSilent_620_);
v_res_626_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(v_ref_617_, v_msgData_618_, v_severity_boxed_624_, v_isSilent_boxed_625_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v_ref_617_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(lean_object* v_ref_627_, lean_object* v_msgData_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
uint8_t v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = 1;
v___x_633_ = 0;
v___x_634_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7(v_ref_627_, v_msgData_628_, v___x_632_, v___x_633_, v___y_629_, v___y_630_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5___boxed(lean_object* v_ref_635_, lean_object* v_msgData_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_ref_635_, v_msgData_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v_ref_635_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__0));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__2));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object* v_linterOption_647_, lean_object* v_stx_648_, lean_object* v_msg_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_name_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_671_; 
v_name_653_ = lean_ctor_get(v_linterOption_647_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v_linterOption_647_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_linterOption_647_, 1);
lean_dec(v_unused_672_);
v___x_655_ = v_linterOption_647_;
v_isShared_656_ = v_isSharedCheck_671_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_name_653_);
lean_dec(v_linterOption_647_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_671_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_657_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__1);
lean_inc(v_name_653_);
v___x_658_ = l_Lean_MessageData_ofName(v_name_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 7);
lean_ctor_set(v___x_655_, 1, v___x_658_);
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_670_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_disable_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_661_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___closed__3);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v_disable_663_ = l_Lean_MessageData_note(v___x_662_);
v___x_664_ = l_Lean_Linter_linterMessageTag;
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v_msg_649_);
lean_ctor_set(v___x_665_, 1, v_disable_663_);
v___x_666_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_667_, 0, v_name_653_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v_stx_648_);
v___x_668_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_668_, 0, v_stx_648_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5(v_stx_648_, v___x_668_, v___y_650_, v___y_651_);
lean_dec(v_stx_648_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object* v_linterOption_673_, lean_object* v_stx_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_linterOption_673_, v_stx_674_, v_msg_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
if (lean_obj_tag(v_a_680_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_array_to_list(v_a_681_);
return v___x_682_;
}
else
{
lean_object* v_head_683_; lean_object* v_tail_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; uint8_t v___x_687_; 
v_head_683_ = lean_ctor_get(v_a_680_, 0);
lean_inc(v_head_683_);
v_tail_684_ = lean_ctor_get(v_a_680_, 1);
lean_inc(v_tail_684_);
lean_dec_ref_known(v_a_680_, 2);
v_fst_685_ = lean_ctor_get(v_head_683_, 0);
lean_inc(v_fst_685_);
v_snd_686_ = lean_ctor_get(v_head_683_, 1);
lean_inc(v_snd_686_);
lean_dec(v_head_683_);
v___x_687_ = lean_name_eq(v_fst_685_, v_snd_686_);
lean_dec(v_snd_686_);
if (v___x_687_ == 0)
{
lean_dec(v_fst_685_);
v_a_680_ = v_tail_684_;
goto _start;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_array_push(v_a_681_, v_fst_685_);
v_a_680_ = v_tail_684_;
v_a_681_ = v___x_689_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object* v_comp_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
if (lean_obj_tag(v_a_692_) == 0)
{
return v_a_693_;
}
else
{
lean_object* v_head_694_; lean_object* v_tail_695_; uint8_t v___x_696_; 
v_head_694_ = lean_ctor_get(v_a_692_, 0);
v_tail_695_ = lean_ctor_get(v_a_692_, 1);
v___x_696_ = lean_name_eq(v_head_694_, v_comp_691_);
if (v___x_696_ == 0)
{
v_a_692_ = v_tail_695_;
goto _start;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_add(v_a_693_, v___x_698_);
lean_dec(v_a_693_);
v_a_692_ = v_tail_695_;
v_a_693_ = v___x_699_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6___boxed(lean_object* v_comp_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v_comp_701_, v_a_702_, v_a_703_);
lean_dec(v_a_702_);
lean_dec(v_comp_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object* v___x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
if (lean_obj_tag(v_a_706_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = l_List_reverse___redArg(v_a_707_);
return v___x_708_;
}
else
{
lean_object* v_head_709_; lean_object* v_tail_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_723_; 
v_head_709_ = lean_ctor_get(v_a_706_, 0);
v_tail_710_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_723_ == 0)
{
v___x_712_ = v_a_706_;
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_tail_710_);
lean_inc(v_head_709_);
lean_dec(v_a_706_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_723_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v_head_709_, v___x_705_, v___x_715_);
v___x_717_ = lean_nat_dec_lt(v___x_714_, v___x_716_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
lean_del_object(v___x_712_);
lean_dec(v_head_709_);
v_a_706_ = v_tail_710_;
goto _start;
}
else
{
lean_object* v___x_720_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v_a_707_);
v___x_720_ = v___x_712_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_head_709_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_a_707_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_a_706_ = v_tail_710_;
v_a_707_ = v___x_720_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object* v___x_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_724_, v_a_725_, v_a_726_);
lean_dec(v___x_724_);
return v_res_727_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_List_reverse___redArg(v_a_732_);
return v___x_733_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_747_; 
v_head_734_ = lean_ctor_get(v_a_731_, 0);
v_tail_735_ = lean_ctor_get(v_a_731_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_747_ == 0)
{
v___x_737_ = v_a_731_;
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
lean_dec(v_a_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_739_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1, &l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
v___x_740_ = l_Lean_MessageData_ofName(v_head_734_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_739_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_a_732_);
lean_ctor_set(v___x_737_, 0, v___x_742_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_a_732_);
v___x_744_ = v_reuseFailAlloc_746_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
v_a_731_ = v_tail_735_;
v_a_732_ = v___x_744_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(uint8_t v___x_765_, lean_object* v_as_766_, size_t v_sz_767_, size_t v_i_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_a_774_; uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_lt(v_i_768_, v_sz_767_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_b_769_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_780_ = lean_box(0);
v_a_781_ = lean_array_uget_borrowed(v_as_766_, v_i_768_);
v___x_782_ = l_Lean_Syntax_getId(v_a_781_);
v___x_783_ = l_Lean_Name_hasMacroScopes(v___x_782_);
if (v___x_783_ == 0)
{
uint8_t v___x_784_; 
v___x_784_ = l_Lean_isPrivateName(v___x_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_786_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___redArg(v___x_785_, v___x_765_, v___y_771_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___y_790_; lean_object* v___x_822_; lean_object* v___y_824_; uint8_t v___x_828_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
lean_inc(v___x_782_);
v___x_822_ = l_Lean_Name_components(v___x_782_);
v___x_828_ = lean_unbox(v_a_787_);
lean_dec(v_a_787_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
lean_inc(v___x_822_);
v___x_830_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_822_, v___x_822_, v___x_829_);
lean_dec(v___x_822_);
v___x_831_ = l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(v___x_830_);
v___y_790_ = v___x_831_;
goto v___jp_789_;
}
else
{
if (lean_obj_tag(v___x_822_) == 0)
{
v___y_824_ = v___x_822_;
goto v___jp_823_;
}
else
{
lean_object* v_tail_832_; 
v_tail_832_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_tail_832_);
v___y_824_ = v_tail_832_;
goto v___jp_823_;
}
}
v___jp_789_:
{
if (lean_obj_tag(v___y_790_) == 0)
{
lean_dec(v___x_782_);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
lean_object* v_tail_791_; 
v_tail_791_ = lean_ctor_get(v___y_790_, 1);
if (lean_obj_tag(v_tail_791_) == 0)
{
lean_object* v_head_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_808_; 
v_head_792_ = lean_ctor_get(v___y_790_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___y_790_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___y_790_, 1);
lean_dec(v_unused_809_);
v___x_794_ = v___y_790_;
v_isShared_795_ = v_isSharedCheck_808_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_head_792_);
lean_dec(v___y_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_808_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1);
v___x_797_ = l_Lean_MessageData_ofName(v_head_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 7);
lean_ctor_set(v___x_794_, 1, v___x_797_);
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_807_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_MessageData_ofConstName(v___x_782_, v___x_765_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_inc(v_a_781_);
v___x_806_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_788_, v_a_781_, v___x_805_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_dec_ref_known(v___x_806_, 1);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_810_ = lean_box(0);
v___x_811_ = l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___y_790_, v___x_810_);
v___x_812_ = l_Lean_MessageData_andList(v___x_811_);
v___x_813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
v___x_815_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_MessageData_ofConstName(v___x_782_, v___x_765_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_inc(v_a_781_);
v___x_821_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v___x_788_, v_a_781_, v___x_820_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_dec_ref_known(v___x_821_, 1);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
return v___x_821_;
}
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v___x_822_, v___y_824_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10));
v___x_827_ = l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v___x_825_, v___x_826_);
v___y_790_ = v___x_827_;
goto v___jp_789_;
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v___x_782_);
v_a_833_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_786_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_786_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_dec(v___x_782_);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
}
else
{
lean_dec(v___x_782_);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
}
v___jp_773_:
{
size_t v___x_775_; size_t v___x_776_; 
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_768_, v___x_775_);
v_i_768_ = v___x_776_;
v_b_769_ = v_a_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___boxed(lean_object* v___x_841_, lean_object* v_as_842_, lean_object* v_sz_843_, lean_object* v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___x_8468__boxed_849_; size_t v_sz_boxed_850_; size_t v_i_boxed_851_; lean_object* v_res_852_; 
v___x_8468__boxed_849_ = lean_unbox(v___x_841_);
v_sz_boxed_850_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_851_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_8468__boxed_849_, v_as_842_, v_sz_boxed_850_, v_i_boxed_851_, v_b_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_as_842_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object* v___x_853_, lean_object* v_pos_854_, lean_object* v_init_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_d_859_; 
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v_k_862_; lean_object* v_v_863_; lean_object* v_l_864_; lean_object* v_r_865_; lean_object* v___x_866_; lean_object* v_a_867_; 
v_k_862_ = lean_ctor_get(v_x_856_, 1);
lean_inc(v_k_862_);
v_v_863_ = lean_ctor_get(v_x_856_, 2);
lean_inc(v_v_863_);
v_l_864_ = lean_ctor_get(v_x_856_, 3);
lean_inc(v_l_864_);
v_r_865_ = lean_ctor_get(v_x_856_, 4);
lean_inc(v_r_865_);
lean_dec_ref_known(v_x_856_, 5);
v___x_866_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_853_, v_pos_854_, v_init_855_, v_l_864_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v_a_868_; 
lean_dec_ref(v___x_866_);
lean_dec(v_r_865_);
lean_dec(v_v_863_);
lean_dec(v_k_862_);
v_a_868_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v_a_867_, 1);
v_d_859_ = v_a_868_;
goto v___jp_858_;
}
else
{
lean_object* v_range_869_; lean_object* v_a_870_; lean_object* v_selectionRange_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_894_; 
v_range_869_ = lean_ctor_get(v_v_863_, 0);
lean_inc_ref(v_range_869_);
v_a_870_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v_a_867_, 1);
v_selectionRange_871_ = lean_ctor_get(v_v_863_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_v_863_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_v_863_, 0);
lean_dec(v_unused_895_);
v___x_873_ = v_v_863_;
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_selectionRange_871_);
lean_dec(v_v_863_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_pos_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_pos_875_ = lean_ctor_get(v_range_869_, 0);
lean_inc_ref(v_pos_875_);
lean_dec_ref(v_range_869_);
v___x_876_ = l_Lean_FileMap_ofPosition(v___x_853_, v_pos_875_);
v___x_877_ = lean_nat_dec_le(v_pos_854_, v___x_876_);
lean_dec(v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v_a_878_; 
lean_del_object(v___x_873_);
lean_dec_ref(v_selectionRange_871_);
lean_dec(v_a_870_);
lean_dec(v_k_862_);
v_a_878_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_866_);
if (lean_obj_tag(v_a_878_) == 0)
{
lean_object* v_a_879_; 
lean_dec(v_r_865_);
v_a_879_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v_a_878_, 1);
v_d_859_ = v_a_879_;
goto v___jp_858_;
}
else
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v_a_878_, 1);
v_init_855_ = v_a_880_;
v_x_856_ = v_r_865_;
goto _start;
}
}
else
{
lean_object* v_pos_882_; lean_object* v_endPos_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec_ref(v___x_866_);
v_pos_882_ = lean_ctor_get(v_selectionRange_871_, 0);
lean_inc_ref(v_pos_882_);
v_endPos_883_ = lean_ctor_get(v_selectionRange_871_, 2);
lean_inc_ref(v_endPos_883_);
lean_dec_ref(v_selectionRange_871_);
v___x_884_ = l_Lean_FileMap_ofPosition(v___x_853_, v_pos_882_);
v___x_885_ = l_Lean_FileMap_ofPosition(v___x_853_, v_endPos_883_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___x_885_);
lean_ctor_set(v___x_873_, 0, v___x_884_);
v___x_887_ = v___x_873_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_893_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_888_ = l_Lean_Syntax_ofRange(v___x_887_, v___x_877_);
v___x_889_ = 0;
v___x_890_ = l_Lean_mkIdentFrom(v___x_888_, v_k_862_, v___x_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_array_push(v_a_870_, v___x_890_);
v_init_855_ = v___x_891_;
v_x_856_ = v_r_865_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_init_855_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_d_859_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object* v___x_898_, lean_object* v_pos_899_, lean_object* v_init_900_, lean_object* v_x_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_898_, v_pos_899_, v_init_900_, v_x_901_);
lean_dec(v_pos_899_);
lean_dec_ref(v___x_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object* v_pos_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_env_909_; lean_object* v_fileMap_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_drs_915_; lean_object* v_nms_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v___x_908_ = lean_st_ref_get(v___y_906_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_908_);
v_fileMap_910_ = lean_ctor_get(v___y_905_, 1);
v___x_911_ = lean_box(1);
v___x_912_ = l_Lean_declRangeExt;
v___x_913_ = lean_box(1);
v___x_914_ = lean_box(0);
v_drs_915_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_911_, v___x_912_, v_env_909_, v___x_913_, v___x_914_);
v_nms_916_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_917_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_910_, v_pos_904_, v_nms_916_, v_drs_915_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_a_922_; lean_object* v___x_924_; 
v_a_922_ = lean_ctor_get(v_a_918_, 0);
lean_inc(v_a_922_);
lean_dec(v_a_918_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v_a_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object* v_pos_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v_pos_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v_pos_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object* v_o_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v_env_936_; lean_object* v___x_937_; lean_object* v_toEnvExtension_938_; lean_object* v_asyncMode_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_merged_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v___x_935_ = lean_st_ref_get(v___y_933_);
v_env_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_env_936_);
lean_dec(v___x_935_);
v___x_937_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_938_ = lean_ctor_get(v___x_937_, 0);
v_asyncMode_939_ = lean_ctor_get(v_toEnvExtension_938_, 2);
v___x_940_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_940_, v___x_937_, v_env_936_, v_asyncMode_939_, v___x_941_);
v_merged_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_942_, 1);
lean_dec(v_unused_952_);
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_merged_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_merged_943_);
lean_ctor_set(v___x_945_, 0, v_o_932_);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_o_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_merged_943_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object* v_o_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_scopes_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_opts_964_; lean_object* v___x_965_; 
v___x_960_ = lean_st_ref_get(v___y_958_);
v_scopes_961_ = lean_ctor_get(v___x_960_, 2);
lean_inc(v_scopes_961_);
lean_dec(v___x_960_);
v___x_962_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_963_ = l_List_head_x21___redArg(v___x_962_, v_scopes_961_);
lean_dec(v_scopes_961_);
v_opts_964_ = lean_ctor_get(v___x_963_, 1);
lean_inc_ref(v_opts_964_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_opts_964_, v___y_958_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(lean_object* v___f_970_, lean_object* v_stx_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1035_; 
v___x_975_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_972_, v___y_973_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1035_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1035_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v_aliases_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; 
v___x_980_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
v___x_981_ = l_Lean_Linter_getLinterValue(v___x_980_, v_a_976_);
lean_dec(v_a_976_);
if (v___x_981_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_dec(v_stx_971_);
lean_dec_ref(v___f_970_);
v___x_1018_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_1018_);
v___x_1020_ = v___x_978_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
else
{
lean_object* v___x_1022_; 
lean_del_object(v___x_978_);
lean_inc(v_stx_971_);
v___x_1022_ = l_Lean_Syntax_find_x3f(v_stx_971_, v___f_970_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v_val_1023_; lean_object* v___x_1024_; 
v_val_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(v_val_1023_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v_aliases_1011_ = v_a_1025_;
v___y_1012_ = v___y_972_;
v___y_1013_ = v___y_973_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_stx_971_);
v_a_1026_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v___x_1034_; 
lean_dec(v___x_1022_);
v___x_1034_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v_aliases_1011_ = v___x_1034_;
v___y_1012_ = v___y_972_;
v___y_1013_ = v___y_973_;
goto v___jp_1010_;
}
}
v___jp_982_:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v___y_986_, v___y_985_, v___y_983_);
lean_dec(v___y_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Array_append___redArg(v_a_988_, v___y_984_);
lean_dec_ref(v___y_984_);
v___x_990_ = lean_box(0);
v_sz_991_ = lean_array_size(v___x_989_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_981_, v___x_989_, v_sz_991_, v___x_992_, v___x_990_, v___y_985_, v___y_983_);
lean_dec_ref(v___x_989_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1001_);
v___x_995_ = v___x_993_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_993_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_990_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_990_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
return v___x_993_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v___y_984_);
v_a_1002_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_987_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_987_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
v___jp_1010_:
{
uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = 0;
v___x_1015_ = l_Lean_Syntax_getPos_x3f(v_stx_971_, v___x_1014_);
lean_dec(v_stx_971_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_unsigned_to_nat(0u);
v___y_983_ = v___y_1013_;
v___y_984_ = v_aliases_1011_;
v___y_985_ = v___y_1012_;
v___y_986_ = v___x_1016_;
goto v___jp_982_;
}
else
{
lean_object* v_val_1017_; 
v_val_1017_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v___x_1015_, 1);
v___y_983_ = v___y_1013_;
v___y_984_ = v_aliases_1011_;
v___y_985_ = v___y_1012_;
v___y_986_ = v_val_1017_;
goto v___jp_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(lean_object* v___f_1036_, lean_object* v_stx_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(v___f_1036_, v_stx_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object* v_o_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_1058_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object* v_o_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(v_o_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object* v___x_1068_, lean_object* v_pos_1069_, lean_object* v_init_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1068_, v_pos_1069_, v_init_1070_, v_x_1071_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object* v___x_1076_, lean_object* v_pos_1077_, lean_object* v_init_1078_, lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(v___x_1076_, v_pos_1077_, v_init_1078_, v_x_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_pos_1077_);
lean_dec_ref(v___x_1076_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(uint8_t v___x_1084_, lean_object* v___x_1085_, lean_object* v_as_1086_, size_t v_sz_1087_, size_t v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_1084_, v___x_1085_, v_as_1086_, v_sz_1087_, v_i_1088_, v_b_1089_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___boxed(lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v_as_1096_, lean_object* v_sz_1097_, lean_object* v_i_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_9026__boxed_1103_; size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v___x_9026__boxed_1103_ = lean_unbox(v___x_1094_);
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1097_);
lean_dec(v_sz_1097_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(v___x_9026__boxed_1103_, v___x_1095_, v_as_1096_, v_sz_boxed_1104_, v_i_boxed_1105_, v_b_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec_ref(v_as_1096_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14(lean_object* v_msgData_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___redArg(v_msgData_1107_, v___y_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14___boxed(lean_object* v_msgData_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3_spec__5_spec__7_spec__14(v_msgData_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace));
v___x_1119_ = l_Lean_Elab_Command_addLinter(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
return v_res_1121_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
