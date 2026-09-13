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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
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
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0 = (const lean_object*)&l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(lean_object* v_k_266_, uint8_t v_defValue_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_scopes_272_; lean_object* v___x_273_; lean_object* v_opts_274_; lean_object* v_map_275_; lean_object* v___x_276_; 
v___x_270_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_271_ = lean_st_ref_get(v___y_268_);
v_scopes_272_ = lean_ctor_get(v___x_271_, 2);
lean_inc(v_scopes_272_);
lean_dec(v___x_271_);
v___x_273_ = l_List_head_x21___redArg(v___x_270_, v_scopes_272_);
lean_dec(v_scopes_272_);
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
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg___boxed(lean_object* v_k_293_, lean_object* v_defValue_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v_defValue_boxed_297_; lean_object* v_res_298_; 
v_defValue_boxed_297_ = lean_unbox(v_defValue_294_);
v_res_298_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v_k_293_, v_defValue_boxed_297_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v_k_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object* v_k_299_, uint8_t v_defValue_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v_k_299_, v_defValue_300_, v___y_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object* v_k_305_, lean_object* v_defValue_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v_defValue_boxed_310_; lean_object* v_res_311_; 
v_defValue_boxed_310_ = lean_unbox(v_defValue_306_);
v_res_311_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_k_305_, v_defValue_boxed_310_, v___y_307_, v___y_308_);
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
uint8_t v___x_7728__boxed_353_; size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v___x_7728__boxed_353_ = lean_unbox(v___x_346_);
v_sz_boxed_354_ = lean_unbox_usize(v_sz_349_);
lean_dec(v_sz_349_);
v_i_boxed_355_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_7728__boxed_353_, v___x_347_, v_as_348_, v_sz_boxed_354_, v_i_boxed_355_, v_b_351_);
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
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_ids_367_; lean_object* v___x_368_; 
v___x_365_ = lean_unsigned_to_nat(3u);
v___x_366_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_365_);
lean_dec(v_stx_357_);
v_ids_367_ = l_Lean_Syntax_getArgs(v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = l_Lean_Elab_Command_getScope___redArg(v___y_359_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_currNamespace_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v_currNamespace_370_ = lean_ctor_get(v_a_369_, 2);
lean_inc(v_currNamespace_370_);
lean_dec(v_a_369_);
v_sz_371_ = lean_array_size(v_ids_367_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_363_, v_currNamespace_370_, v_ids_367_, v_sz_371_, v___x_372_, v_aliases_361_);
lean_dec_ref(v_ids_367_);
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
lean_dec_ref(v_ids_367_);
v_a_390_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_368_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_368_);
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
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__0));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
if (lean_obj_tag(v_a_406_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_List_reverse___redArg(v_a_407_);
return v___x_408_;
}
else
{
lean_object* v_head_409_; lean_object* v_tail_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_head_409_ = lean_ctor_get(v_a_406_, 0);
v_tail_410_ = lean_ctor_get(v_a_406_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v_a_406_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_tail_410_);
lean_inc(v_head_409_);
lean_dec(v_a_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_414_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1, &l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1);
v___x_415_ = l_Lean_MessageData_ofName(v_head_409_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_414_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_a_407_);
lean_ctor_set(v___x_412_, 0, v___x_417_);
v___x_419_ = v___x_412_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_a_407_);
v___x_419_ = v_reuseFailAlloc_421_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v_a_406_ = v_tail_410_;
v_a_407_ = v___x_419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
if (lean_obj_tag(v_a_423_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_array_to_list(v_a_424_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; uint8_t v___x_430_; 
v_head_426_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_head_426_);
v_tail_427_ = lean_ctor_get(v_a_423_, 1);
lean_inc(v_tail_427_);
lean_dec_ref_known(v_a_423_, 2);
v_fst_428_ = lean_ctor_get(v_head_426_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v_head_426_, 1);
lean_inc(v_snd_429_);
lean_dec(v_head_426_);
v___x_430_ = lean_name_eq(v_fst_428_, v_snd_429_);
lean_dec(v_snd_429_);
if (v___x_430_ == 0)
{
lean_dec(v_fst_428_);
v_a_423_ = v_tail_427_;
goto _start;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = lean_array_push(v_a_424_, v_fst_428_);
v_a_423_ = v_tail_427_;
v_a_424_ = v___x_432_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(lean_object* v_opts_434_, lean_object* v_opt_435_){
_start:
{
lean_object* v_name_436_; lean_object* v_defValue_437_; lean_object* v_map_438_; lean_object* v___x_439_; 
v_name_436_ = lean_ctor_get(v_opt_435_, 0);
v_defValue_437_ = lean_ctor_get(v_opt_435_, 1);
v_map_438_ = lean_ctor_get(v_opts_434_, 0);
v___x_439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_438_, v_name_436_);
if (lean_obj_tag(v___x_439_) == 0)
{
uint8_t v___x_440_; 
v___x_440_ = lean_unbox(v_defValue_437_);
return v___x_440_;
}
else
{
lean_object* v_val_441_; 
v_val_441_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_441_);
lean_dec_ref_known(v___x_439_, 1);
if (lean_obj_tag(v_val_441_) == 1)
{
uint8_t v_v_442_; 
v_v_442_ = lean_ctor_get_uint8(v_val_441_, 0);
lean_dec_ref_known(v_val_441_, 0);
return v_v_442_;
}
else
{
uint8_t v___x_443_; 
lean_dec(v_val_441_);
v___x_443_ = lean_unbox(v_defValue_437_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15___boxed(lean_object* v_opts_444_, lean_object* v_opt_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(v_opts_444_, v_opt_445_);
lean_dec_ref(v_opt_445_);
lean_dec_ref(v_opts_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0(uint8_t v_suppressElabErrors_449_, uint8_t v___y_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 1)
{
lean_object* v_pre_452_; 
v_pre_452_ = lean_ctor_get(v_x_451_, 0);
if (lean_obj_tag(v_pre_452_) == 0)
{
lean_object* v_str_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_str_453_ = lean_ctor_get(v_x_451_, 1);
v___x_454_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___closed__0));
v___x_455_ = lean_string_dec_eq(v_str_453_, v___x_454_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
return v_suppressElabErrors_449_;
}
}
else
{
return v___y_450_;
}
}
else
{
return v___y_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___boxed(lean_object* v_suppressElabErrors_456_, lean_object* v___y_457_, lean_object* v_x_458_){
_start:
{
uint8_t v_suppressElabErrors_boxed_459_; uint8_t v___y_7936__boxed_460_; uint8_t v_res_461_; lean_object* v_r_462_; 
v_suppressElabErrors_boxed_459_ = lean_unbox(v_suppressElabErrors_456_);
v___y_7936__boxed_460_ = lean_unbox(v___y_457_);
v_res_461_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0(v_suppressElabErrors_boxed_459_, v___y_7936__boxed_460_, v_x_458_);
lean_dec(v_x_458_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_463_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
lean_ctor_set(v___x_468_, 3, v___x_467_);
lean_ctor_set(v___x_468_, 4, v___x_466_);
lean_ctor_set(v___x_468_, 5, v___x_466_);
lean_ctor_set(v___x_468_, 6, v___x_466_);
lean_ctor_set(v___x_468_, 7, v___x_466_);
lean_ctor_set(v___x_468_, 8, v___x_466_);
lean_ctor_set(v___x_468_, 9, v___x_466_);
lean_ctor_set(v___x_468_, 10, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(32u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4(void){
_start:
{
size_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = ((size_t)5ULL);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_unsigned_to_nat(32u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_476_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3);
v___x_477_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_473_);
lean_ctor_set(v___x_477_, 3, v___x_473_);
lean_ctor_set_usize(v___x_477_, 4, v___x_472_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_box(1);
v___x_479_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4);
v___x_480_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1);
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_msgData_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_env_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_scopes_489_; lean_object* v___x_490_; lean_object* v_opts_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_485_ = lean_st_ref_get(v___y_483_);
v_env_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_485_);
v___x_487_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_488_ = lean_st_ref_get(v___y_483_);
v_scopes_489_ = lean_ctor_get(v___x_488_, 2);
lean_inc(v_scopes_489_);
lean_dec(v___x_488_);
v___x_490_ = l_List_head_x21___redArg(v___x_487_, v_scopes_489_);
lean_dec(v_scopes_489_);
v_opts_491_ = lean_ctor_get(v___x_490_, 1);
lean_inc_ref(v_opts_491_);
lean_dec(v___x_490_);
v___x_492_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2);
v___x_493_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5);
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v_env_486_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
lean_ctor_set(v___x_494_, 3, v_opts_491_);
v___x_495_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_msgData_482_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_msgData_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v_msgData_497_, v___y_498_);
lean_dec(v___y_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(lean_object* v_ref_502_, lean_object* v_msgData_503_, uint8_t v_severity_504_, uint8_t v_isSilent_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; uint8_t v___y_575_; lean_object* v___y_576_; uint8_t v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; uint8_t v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; uint8_t v___y_611_; uint8_t v___y_612_; uint8_t v___y_613_; uint8_t v___x_628_; uint8_t v___y_630_; uint8_t v___y_631_; uint8_t v___y_632_; uint8_t v___y_634_; uint8_t v___x_646_; 
v___x_628_ = 2;
v___x_646_ = l_Lean_instBEqMessageSeverity_beq(v_severity_504_, v___x_628_);
if (v___x_646_ == 0)
{
v___y_634_ = v___x_646_;
goto v___jp_633_;
}
else
{
uint8_t v___x_647_; 
lean_inc_ref(v_msgData_503_);
v___x_647_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_503_);
v___y_634_ = v___x_647_;
goto v___jp_633_;
}
v___jp_509_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Elab_Command_getScope___redArg(v___y_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v_currNamespace_520_; lean_object* v___x_521_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v_currNamespace_520_ = lean_ctor_get(v_a_519_, 2);
lean_inc(v_currNamespace_520_);
lean_dec(v_a_519_);
v___x_521_ = l_Lean_Elab_Command_getScope___redArg(v___y_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_557_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_557_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_557_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_557_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_openDecls_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_env_531_; lean_object* v_messages_532_; lean_object* v_scopes_533_; lean_object* v_usedQuotCtxts_534_; lean_object* v_nextMacroScope_535_; lean_object* v_maxRecDepth_536_; lean_object* v_ngen_537_; lean_object* v_auxDeclNGen_538_; lean_object* v_infoState_539_; lean_object* v_traceState_540_; lean_object* v_snapshotTasks_541_; lean_object* v_prevLinterStates_542_; lean_object* v_codeQualityEntryTasks_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_556_; 
v_openDecls_526_ = lean_ctor_get(v_a_522_, 3);
lean_inc(v_openDecls_526_);
lean_dec(v_a_522_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_currNamespace_520_);
lean_ctor_set(v___x_527_, 1, v_openDecls_526_);
v___x_528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc_ref(v___y_514_);
v___x_529_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_529_, 0, v___y_514_);
lean_ctor_set(v___x_529_, 1, v___y_513_);
lean_ctor_set(v___x_529_, 2, v___y_512_);
lean_ctor_set(v___x_529_, 3, v___y_510_);
lean_ctor_set(v___x_529_, 4, v___x_528_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*5, v___y_516_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*5 + 1, v___y_515_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*5 + 2, v_isSilent_505_);
v___x_530_ = lean_st_ref_take(v___y_517_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
v_messages_532_ = lean_ctor_get(v___x_530_, 1);
v_scopes_533_ = lean_ctor_get(v___x_530_, 2);
v_usedQuotCtxts_534_ = lean_ctor_get(v___x_530_, 3);
v_nextMacroScope_535_ = lean_ctor_get(v___x_530_, 4);
v_maxRecDepth_536_ = lean_ctor_get(v___x_530_, 5);
v_ngen_537_ = lean_ctor_get(v___x_530_, 6);
v_auxDeclNGen_538_ = lean_ctor_get(v___x_530_, 7);
v_infoState_539_ = lean_ctor_get(v___x_530_, 8);
v_traceState_540_ = lean_ctor_get(v___x_530_, 9);
v_snapshotTasks_541_ = lean_ctor_get(v___x_530_, 10);
v_prevLinterStates_542_ = lean_ctor_get(v___x_530_, 11);
v_codeQualityEntryTasks_543_ = lean_ctor_get(v___x_530_, 12);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_556_ == 0)
{
v___x_545_ = v___x_530_;
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_codeQualityEntryTasks_543_);
lean_inc(v_prevLinterStates_542_);
lean_inc(v_snapshotTasks_541_);
lean_inc(v_traceState_540_);
lean_inc(v_infoState_539_);
lean_inc(v_auxDeclNGen_538_);
lean_inc(v_ngen_537_);
lean_inc(v_maxRecDepth_536_);
lean_inc(v_nextMacroScope_535_);
lean_inc(v_usedQuotCtxts_534_);
lean_inc(v_scopes_533_);
lean_inc(v_messages_532_);
lean_inc(v_env_531_);
lean_dec(v___x_530_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_556_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = lean_box(0);
v___x_548_ = l_Lean_MessageLog_add(v___x_529_, v_messages_532_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_env_531_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_scopes_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_usedQuotCtxts_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_nextMacroScope_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_maxRecDepth_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_ngen_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_auxDeclNGen_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_infoState_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 9, v_traceState_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 10, v_snapshotTasks_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 11, v_prevLinterStates_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 12, v_codeQualityEntryTasks_543_);
v___x_550_ = v_reuseFailAlloc_555_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_st_ref_put(v___y_517_, v___x_550_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_547_);
v___x_553_ = v___x_524_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_547_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_currNamespace_520_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
v_a_558_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_521_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_521_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
v_a_566_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_518_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_518_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
v___jp_574_:
{
lean_object* v_fileName_580_; lean_object* v_fileMap_581_; uint8_t v_suppressElabErrors_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_601_; 
v_fileName_580_ = lean_ctor_get(v___y_506_, 0);
v_fileMap_581_ = lean_ctor_get(v___y_506_, 1);
v_suppressElabErrors_582_ = lean_ctor_get_uint8(v___y_506_, sizeof(void*)*10);
v___x_583_ = lean_box(v_suppressElabErrors_582_);
v___x_584_ = lean_box(v___y_575_);
v___f_585_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___boxed), 3, 2);
lean_closure_set(v___f_585_, 0, v___x_583_);
lean_closure_set(v___f_585_, 1, v___x_584_);
v___x_586_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_503_);
v___x_587_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v___x_586_, v___y_507_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_601_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_601_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_601_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_inc_ref_n(v_fileMap_581_, 2);
v___x_592_ = l_Lean_FileMap_toPosition(v_fileMap_581_, v___y_576_);
lean_dec(v___y_576_);
v___x_593_ = l_Lean_FileMap_toPosition(v_fileMap_581_, v___y_579_);
lean_dec(v___y_579_);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___closed__0));
if (v_suppressElabErrors_582_ == 0)
{
lean_del_object(v___x_590_);
lean_dec_ref(v___f_585_);
v___y_510_ = v___x_595_;
v___y_511_ = v_a_588_;
v___y_512_ = v___x_594_;
v___y_513_ = v___x_592_;
v___y_514_ = v_fileName_580_;
v___y_515_ = v___y_577_;
v___y_516_ = v___y_578_;
v___y_517_ = v___y_507_;
goto v___jp_509_;
}
else
{
uint8_t v___x_596_; 
lean_inc(v_a_588_);
v___x_596_ = l_Lean_MessageData_hasTag(v___f_585_, v_a_588_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec_ref_known(v___x_594_, 1);
lean_dec_ref(v___x_592_);
lean_dec(v_a_588_);
v___x_597_ = lean_box(0);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_599_ = v___x_590_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_del_object(v___x_590_);
v___y_510_ = v___x_595_;
v___y_511_ = v_a_588_;
v___y_512_ = v___x_594_;
v___y_513_ = v___x_592_;
v___y_514_ = v_fileName_580_;
v___y_515_ = v___y_577_;
v___y_516_ = v___y_578_;
v___y_517_ = v___y_507_;
goto v___jp_509_;
}
}
}
}
v___jp_602_:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Syntax_getTailPos_x3f(v___y_604_, v___y_606_);
lean_dec(v___y_604_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_inc(v___y_607_);
v___y_575_ = v___y_603_;
v___y_576_ = v___y_607_;
v___y_577_ = v___y_605_;
v___y_578_ = v___y_606_;
v___y_579_ = v___y_607_;
goto v___jp_574_;
}
else
{
lean_object* v_val_609_; 
v_val_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_val_609_);
lean_dec_ref_known(v___x_608_, 1);
v___y_575_ = v___y_603_;
v___y_576_ = v___y_607_;
v___y_577_ = v___y_605_;
v___y_578_ = v___y_606_;
v___y_579_ = v_val_609_;
goto v___jp_574_;
}
}
v___jp_610_:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Elab_Command_getRef___redArg(v___y_506_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_ref_616_; lean_object* v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v_ref_616_ = l_Lean_replaceRef(v_ref_502_, v_a_615_);
lean_dec(v_a_615_);
v___x_617_ = l_Lean_Syntax_getPos_x3f(v_ref_616_, v___y_612_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___y_603_ = v___y_611_;
v___y_604_ = v_ref_616_;
v___y_605_ = v___y_613_;
v___y_606_ = v___y_612_;
v___y_607_ = v___x_618_;
goto v___jp_602_;
}
else
{
lean_object* v_val_619_; 
v_val_619_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_617_, 1);
v___y_603_ = v___y_611_;
v___y_604_ = v_ref_616_;
v___y_605_ = v___y_613_;
v___y_606_ = v___y_612_;
v___y_607_ = v_val_619_;
goto v___jp_602_;
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_msgData_503_);
v_a_620_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_614_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_614_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
v___jp_629_:
{
if (v___y_632_ == 0)
{
v___y_611_ = v___y_630_;
v___y_612_ = v___y_631_;
v___y_613_ = v_severity_504_;
goto v___jp_610_;
}
else
{
v___y_611_ = v___y_630_;
v___y_612_ = v___y_631_;
v___y_613_ = v___x_628_;
goto v___jp_610_;
}
}
v___jp_633_:
{
if (v___y_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_scopes_637_; lean_object* v___x_638_; lean_object* v_opts_639_; uint8_t v___x_640_; uint8_t v___x_641_; 
v___x_635_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_636_ = lean_st_ref_get(v___y_507_);
v_scopes_637_ = lean_ctor_get(v___x_636_, 2);
lean_inc(v_scopes_637_);
lean_dec(v___x_636_);
v___x_638_ = l_List_head_x21___redArg(v___x_635_, v_scopes_637_);
lean_dec(v_scopes_637_);
v_opts_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_opts_639_);
lean_dec(v___x_638_);
v___x_640_ = 1;
v___x_641_ = l_Lean_instBEqMessageSeverity_beq(v_severity_504_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec_ref(v_opts_639_);
v___y_630_ = v___y_634_;
v___y_631_ = v___y_634_;
v___y_632_ = v___x_641_;
goto v___jp_629_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = l_Lean_warningAsError;
v___x_643_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(v_opts_639_, v___x_642_);
lean_dec_ref(v_opts_639_);
v___y_630_ = v___y_634_;
v___y_631_ = v___y_634_;
v___y_632_ = v___x_643_;
goto v___jp_629_;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref(v_msgData_503_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___boxed(lean_object* v_ref_648_, lean_object* v_msgData_649_, lean_object* v_severity_650_, lean_object* v_isSilent_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v_severity_boxed_655_; uint8_t v_isSilent_boxed_656_; lean_object* v_res_657_; 
v_severity_boxed_655_ = lean_unbox(v_severity_650_);
v_isSilent_boxed_656_ = lean_unbox(v_isSilent_651_);
v_res_657_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(v_ref_648_, v_msgData_649_, v_severity_boxed_655_, v_isSilent_boxed_656_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_ref_648_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(lean_object* v_ref_658_, lean_object* v_msgData_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = 1;
v___x_664_ = 0;
v___x_665_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(v_ref_658_, v_msgData_659_, v___x_663_, v___x_664_, v___y_660_, v___y_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6___boxed(lean_object* v_ref_666_, lean_object* v_msgData_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(v_ref_666_, v_msgData_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v_ref_666_);
return v_res_671_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object* v_linterOption_678_, lean_object* v_stx_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_name_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_702_; 
v_name_684_ = lean_ctor_get(v_linterOption_678_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_linterOption_678_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_linterOption_678_, 1);
lean_dec(v_unused_703_);
v___x_686_ = v_linterOption_678_;
v_isShared_687_ = v_isSharedCheck_702_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_name_684_);
lean_dec(v_linterOption_678_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_702_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
lean_inc(v_name_684_);
v___x_689_ = l_Lean_MessageData_ofName(v_name_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 7);
lean_ctor_set(v___x_686_, 1, v___x_689_);
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_701_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_disable_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_692_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v_disable_694_ = l_Lean_MessageData_note(v___x_693_);
v___x_695_ = l_Lean_Linter_linterMessageTag;
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v_msg_680_);
lean_ctor_set(v___x_696_, 1, v_disable_694_);
v___x_697_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_698_, 0, v_name_684_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
lean_inc(v_stx_679_);
v___x_699_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_699_, 0, v_stx_679_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(v_stx_679_, v___x_699_, v___y_681_, v___y_682_);
lean_dec(v_stx_679_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(lean_object* v_linterOption_704_, lean_object* v_stx_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v_linterOption_704_, v_stx_705_, v_msg_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object* v_comp_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
if (lean_obj_tag(v_a_712_) == 0)
{
return v_a_713_;
}
else
{
lean_object* v_head_714_; lean_object* v_tail_715_; uint8_t v___x_716_; 
v_head_714_ = lean_ctor_get(v_a_712_, 0);
v_tail_715_ = lean_ctor_get(v_a_712_, 1);
v___x_716_ = lean_name_eq(v_head_714_, v_comp_711_);
if (v___x_716_ == 0)
{
v_a_712_ = v_tail_715_;
goto _start;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_a_713_, v___x_718_);
lean_dec(v_a_713_);
v_a_712_ = v_tail_715_;
v_a_713_ = v___x_719_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object* v_comp_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_comp_721_, v_a_722_, v_a_723_);
lean_dec(v_a_722_);
lean_dec(v_comp_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object* v___x_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
if (lean_obj_tag(v_a_726_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = l_List_reverse___redArg(v_a_727_);
return v___x_728_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_743_; 
v_head_729_ = lean_ctor_get(v_a_726_, 0);
v_tail_730_ = lean_ctor_get(v_a_726_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_743_ == 0)
{
v___x_732_ = v_a_726_;
v_isShared_733_ = v_isSharedCheck_743_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_tail_730_);
lean_inc(v_head_729_);
lean_dec(v_a_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_743_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_head_729_, v___x_725_, v___x_735_);
v___x_737_ = lean_nat_dec_lt(v___x_734_, v___x_736_);
lean_dec(v___x_736_);
if (v___x_737_ == 0)
{
lean_del_object(v___x_732_);
lean_dec(v_head_729_);
v_a_726_ = v_tail_730_;
goto _start;
}
else
{
lean_object* v___x_740_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v_a_727_);
v___x_740_ = v___x_732_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_head_729_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_727_);
v___x_740_ = v_reuseFailAlloc_742_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v_a_726_ = v_tail_730_;
v_a_727_ = v___x_740_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object* v___x_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_744_, v_a_745_, v_a_746_);
lean_dec(v___x_744_);
return v_res_747_;
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
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
lean_inc(v___x_782_);
v___x_786_ = l_Lean_Name_components(v___x_782_);
v___x_787_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_788_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v___x_787_, v___x_765_, v___y_771_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___y_791_; lean_object* v___y_824_; uint8_t v___x_828_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_828_ = lean_unbox(v_a_789_);
lean_dec(v_a_789_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
lean_inc(v___x_786_);
v___x_830_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_786_, v___x_786_, v___x_829_);
lean_dec(v___x_786_);
v___x_831_ = l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(v___x_830_);
v___y_791_ = v___x_831_;
goto v___jp_790_;
}
else
{
if (lean_obj_tag(v___x_786_) == 0)
{
v___y_824_ = v___x_786_;
goto v___jp_823_;
}
else
{
lean_object* v_tail_832_; 
v_tail_832_ = lean_ctor_get(v___x_786_, 1);
lean_inc(v_tail_832_);
v___y_824_ = v_tail_832_;
goto v___jp_823_;
}
}
v___jp_790_:
{
if (lean_obj_tag(v___y_791_) == 0)
{
lean_dec(v___x_782_);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
lean_object* v_tail_792_; 
v_tail_792_ = lean_ctor_get(v___y_791_, 1);
if (lean_obj_tag(v_tail_792_) == 0)
{
lean_object* v_head_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_809_; 
v_head_793_ = lean_ctor_get(v___y_791_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___y_791_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___y_791_, 1);
lean_dec(v_unused_810_);
v___x_795_ = v___y_791_;
v_isShared_796_ = v_isSharedCheck_809_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_head_793_);
lean_dec(v___y_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_809_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1);
v___x_798_ = l_Lean_MessageData_ofName(v_head_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v___x_798_);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_808_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_MessageData_ofConstName(v___x_782_, v___x_765_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
lean_inc(v_a_781_);
v___x_807_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_785_, v_a_781_, v___x_806_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_dec_ref_known(v___x_807_, 1);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_811_ = lean_box(0);
v___x_812_ = l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v___y_791_, v___x_811_);
v___x_813_ = l_Lean_MessageData_andList(v___x_812_);
v___x_814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
v___x_816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_MessageData_ofConstName(v___x_782_, v___x_765_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
lean_inc(v_a_781_);
v___x_822_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_785_, v_a_781_, v___x_821_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref_known(v___x_822_, 1);
v_a_774_ = v___x_780_;
goto v___jp_773_;
}
else
{
return v___x_822_;
}
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v___x_786_, v___y_824_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10));
v___x_827_ = l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v___x_825_, v___x_826_);
v___y_791_ = v___x_827_;
goto v___jp_790_;
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v___x_786_);
lean_dec(v___x_782_);
v_a_833_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_788_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_788_);
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
uint8_t v___x_8490__boxed_849_; size_t v_sz_boxed_850_; size_t v_i_boxed_851_; lean_object* v_res_852_; 
v___x_8490__boxed_849_ = lean_unbox(v___x_841_);
v_sz_boxed_850_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_851_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_8490__boxed_849_, v_as_842_, v_sz_boxed_850_, v_i_boxed_851_, v_b_845_, v___y_846_, v___y_847_);
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
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_env_910_; lean_object* v_fileMap_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_drs_915_; lean_object* v_nms_916_; lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v___x_908_ = lean_box(1);
v___x_909_ = lean_st_ref_get(v___y_906_);
v_env_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_ref(v_env_910_);
lean_dec(v___x_909_);
v_fileMap_911_ = lean_ctor_get(v___y_905_, 1);
v___x_912_ = l_Lean_declRangeExt;
v___x_913_ = lean_box(1);
v___x_914_ = lean_box(0);
v_drs_915_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_908_, v___x_912_, v_env_910_, v___x_913_, v___x_914_);
v_nms_916_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_917_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_911_, v_pos_904_, v_nms_916_, v_drs_915_);
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
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_env_937_; lean_object* v___x_938_; lean_object* v_toEnvExtension_939_; lean_object* v_asyncMode_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_merged_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v___x_935_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_936_ = lean_st_ref_get(v___y_933_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_env_937_);
lean_dec(v___x_936_);
v___x_938_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_939_ = lean_ctor_get(v___x_938_, 0);
v_asyncMode_940_ = lean_ctor_get(v_toEnvExtension_939_, 2);
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_935_, v___x_938_, v_env_937_, v_asyncMode_940_, v___x_941_);
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
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_scopes_962_; lean_object* v___x_963_; lean_object* v_opts_964_; lean_object* v___x_965_; 
v___x_960_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_961_ = lean_st_ref_get(v___y_958_);
v_scopes_962_ = lean_ctor_get(v___x_961_, 2);
lean_inc(v_scopes_962_);
lean_dec(v___x_961_);
v___x_963_ = l_List_head_x21___redArg(v___x_960_, v_scopes_962_);
lean_dec(v_scopes_962_);
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
uint8_t v___x_9048__boxed_1103_; size_t v_sz_boxed_1104_; size_t v_i_boxed_1105_; lean_object* v_res_1106_; 
v___x_9048__boxed_1103_ = lean_unbox(v___x_1094_);
v_sz_boxed_1104_ = lean_unbox_usize(v_sz_1097_);
lean_dec(v_sz_1097_);
v_i_boxed_1105_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_res_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(v___x_9048__boxed_1103_, v___x_1095_, v_as_1096_, v_sz_boxed_1104_, v_i_boxed_1105_, v_b_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec_ref(v_as_1096_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14(lean_object* v_msgData_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v_msgData_1107_, v___y_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_msgData_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14(v_msgData_1112_, v___y_1113_, v___y_1114_);
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
