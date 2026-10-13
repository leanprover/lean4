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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(lean_object* v_fm_98_, lean_object* v_pos_99_, lean_object* v_toPure_100_, uint8_t v___x_101_, lean_object* v_a_102_, lean_object* v_b_103_, lean_object* v_c_104_){
_start:
{
lean_object* v_range_105_; lean_object* v_selectionRange_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_127_; 
v_range_105_ = lean_ctor_get(v_b_103_, 0);
v_selectionRange_106_ = lean_ctor_get(v_b_103_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_b_103_);
if (v_isSharedCheck_127_ == 0)
{
v___x_108_ = v_b_103_;
v_isShared_109_ = v_isSharedCheck_127_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_selectionRange_106_);
lean_inc(v_range_105_);
lean_dec(v_b_103_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_127_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_pos_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_pos_110_ = lean_ctor_get(v_range_105_, 0);
lean_inc_ref(v_pos_110_);
lean_dec_ref(v_range_105_);
v___x_111_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_pos_110_);
v___x_112_ = lean_nat_dec_le(v_pos_99_, v___x_111_);
lean_dec(v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_del_object(v___x_108_);
lean_dec_ref(v_selectionRange_106_);
lean_dec(v_a_102_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_c_104_);
v___x_114_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_pos_115_; lean_object* v_endPos_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v_pos_115_ = lean_ctor_get(v_selectionRange_106_, 0);
lean_inc_ref(v_pos_115_);
v_endPos_116_ = lean_ctor_get(v_selectionRange_106_, 2);
lean_inc_ref(v_endPos_116_);
lean_dec_ref(v_selectionRange_106_);
v___x_117_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_pos_115_);
v___x_118_ = l_Lean_FileMap_ofPosition(v_fm_98_, v_endPos_116_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_118_);
lean_ctor_set(v___x_108_, 0, v___x_117_);
v___x_120_ = v___x_108_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_118_);
v___x_120_ = v_reuseFailAlloc_126_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = l_Lean_Syntax_ofRange(v___x_120_, v___x_112_);
v___x_122_ = l_Lean_mkIdentFrom(v___x_121_, v_a_102_, v___x_101_);
lean_dec(v___x_121_);
v___x_123_ = lean_array_push(v_c_104_, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___x_125_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_124_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed(lean_object* v_fm_128_, lean_object* v_pos_129_, lean_object* v_toPure_130_, lean_object* v___x_131_, lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_c_134_){
_start:
{
uint8_t v___x_209__boxed_135_; lean_object* v_res_136_; 
v___x_209__boxed_135_ = lean_unbox(v___x_131_);
v_res_136_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2(v_fm_128_, v_pos_129_, v_toPure_130_, v___x_209__boxed_135_, v_a_132_, v_b_133_, v_c_134_);
lean_dec(v_pos_129_);
lean_dec_ref(v_fm_128_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(lean_object* v_pos_139_, lean_object* v_toPure_140_, uint8_t v___x_141_, lean_object* v_inst_142_, lean_object* v_drs_143_, lean_object* v_toBind_144_, lean_object* v___f_145_, lean_object* v___f_146_, lean_object* v_fm_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v_nms_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_148_ = lean_box(v___x_141_);
v___f_149_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_149_, 0, v_fm_147_);
lean_closure_set(v___f_149_, 1, v_pos_139_);
lean_closure_set(v___f_149_, 2, v_toPure_140_);
lean_closure_set(v___f_149_, 3, v___x_148_);
v_nms_150_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_151_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_142_, v___f_149_, v_nms_150_, v_drs_143_);
lean_inc(v_toBind_144_);
v___x_152_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_151_, v___f_145_);
v___x_153_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_152_, v___f_146_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___boxed(lean_object* v_pos_154_, lean_object* v_toPure_155_, lean_object* v___x_156_, lean_object* v_inst_157_, lean_object* v_drs_158_, lean_object* v_toBind_159_, lean_object* v___f_160_, lean_object* v___f_161_, lean_object* v_fm_162_){
_start:
{
uint8_t v___x_250__boxed_163_; lean_object* v_res_164_; 
v___x_250__boxed_163_ = lean_unbox(v___x_156_);
v_res_164_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3(v_pos_154_, v_toPure_155_, v___x_250__boxed_163_, v_inst_157_, v_drs_158_, v_toBind_159_, v___f_160_, v___f_161_, v_fm_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4(lean_object* v___x_165_, lean_object* v_pos_166_, lean_object* v_toPure_167_, lean_object* v_inst_168_, lean_object* v_toBind_169_, lean_object* v___f_170_, lean_object* v___f_171_, lean_object* v_inst_172_, lean_object* v_____do__lift_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v_drs_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v___x_174_ = l_Lean_declRangeExt;
v___x_175_ = lean_box(1);
v___x_176_ = lean_box(0);
v___x_177_ = 0;
v_drs_178_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_165_, v___x_174_, v_____do__lift_173_, v___x_175_, v___x_176_, v___x_177_);
v___x_179_ = lean_box(v___x_177_);
lean_inc(v_toBind_169_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_180_, 0, v_pos_166_);
lean_closure_set(v___f_180_, 1, v_toPure_167_);
lean_closure_set(v___f_180_, 2, v___x_179_);
lean_closure_set(v___f_180_, 3, v_inst_168_);
lean_closure_set(v___f_180_, 4, v_drs_178_);
lean_closure_set(v___f_180_, 5, v_toBind_169_);
lean_closure_set(v___f_180_, 6, v___f_170_);
lean_closure_set(v___f_180_, 7, v___f_171_);
v___x_181_ = lean_apply_4(v_toBind_169_, lean_box(0), lean_box(0), v_inst_172_, v___f_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_pos_185_){
_start:
{
lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v_getEnv_188_; lean_object* v_toPure_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_194_; 
v_toApplicative_186_ = lean_ctor_get(v_inst_182_, 0);
v_toBind_187_ = lean_ctor_get(v_inst_182_, 1);
lean_inc_n(v_toBind_187_, 2);
v_getEnv_188_ = lean_ctor_get(v_inst_183_, 0);
lean_inc(v_getEnv_188_);
lean_dec_ref(v_inst_183_);
v_toPure_189_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_inc_n(v_toPure_189_, 3);
v___x_190_ = lean_box(1);
v___f_191_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_191_, 0, v_toPure_189_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_192_, 0, v_toPure_189_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__4), 9, 8);
lean_closure_set(v___f_193_, 0, v___x_190_);
lean_closure_set(v___f_193_, 1, v_pos_185_);
lean_closure_set(v___f_193_, 2, v_toPure_189_);
lean_closure_set(v___f_193_, 3, v_inst_182_);
lean_closure_set(v___f_193_, 4, v_toBind_187_);
lean_closure_set(v___f_193_, 5, v___f_191_);
lean_closure_set(v___f_193_, 6, v___f_192_);
lean_closure_set(v___f_193_, 7, v_inst_184_);
v___x_194_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v_getEnv_188_, v___f_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom(lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_pos_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg(v_inst_196_, v_inst_197_, v_inst_198_, v_pos_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(uint8_t v___x_201_, lean_object* v_currNamespace_202_, lean_object* v_toPure_203_, lean_object* v_a_204_, lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___y_210_; lean_object* v___x_217_; 
v___x_207_ = l_Lean_TSyntax_getId(v_a_204_);
v___x_208_ = 0;
v___x_217_ = l_Lean_Syntax_getRange_x3f(v_a_204_, v___x_208_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_210_ = v___x_218_;
goto v___jp_209_;
}
else
{
lean_object* v_val_219_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 1);
v___y_210_ = v_val_219_;
goto v___jp_209_;
}
v___jp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_211_ = l_Lean_Syntax_ofRange(v___y_210_, v___x_201_);
v___x_212_ = l_Lean_Name_append(v_currNamespace_202_, v___x_207_);
v___x_213_ = l_Lean_mkIdentFrom(v___x_211_, v___x_212_, v___x_208_);
lean_dec(v___x_211_);
v___x_214_ = lean_array_push(v___y_206_, v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed(lean_object* v___x_220_, lean_object* v_currNamespace_221_, lean_object* v_toPure_222_, lean_object* v_a_223_, lean_object* v_x_224_, lean_object* v___y_225_){
_start:
{
uint8_t v___x_215__boxed_226_; lean_object* v_res_227_; 
v___x_215__boxed_226_ = lean_unbox(v___x_220_);
v_res_227_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1(v___x_215__boxed_226_, v_currNamespace_221_, v_toPure_222_, v_a_223_, v_x_224_, v___y_225_);
lean_dec(v_a_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(uint8_t v___x_228_, lean_object* v_toPure_229_, lean_object* v_ids_230_, lean_object* v_inst_231_, lean_object* v_aliases_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_currNamespace_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___f_237_; size_t v_sz_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = lean_box(v___x_228_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_237_, 0, v___x_236_);
lean_closure_set(v___f_237_, 1, v_currNamespace_235_);
lean_closure_set(v___f_237_, 2, v_toPure_229_);
v_sz_238_ = lean_array_size(v_ids_230_);
v___x_239_ = ((size_t)0ULL);
v___x_240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_231_, v_ids_230_, v___f_237_, v_sz_238_, v___x_239_, v_aliases_232_);
v___x_241_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_240_, v___f_234_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed(lean_object* v___x_242_, lean_object* v_toPure_243_, lean_object* v_ids_244_, lean_object* v_inst_245_, lean_object* v_aliases_246_, lean_object* v_toBind_247_, lean_object* v___f_248_, lean_object* v_currNamespace_249_){
_start:
{
uint8_t v___x_250__boxed_250_; lean_object* v_res_251_; 
v___x_250__boxed_250_ = lean_unbox(v___x_242_);
v_res_251_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0(v___x_250__boxed_250_, v_toPure_243_, v_ids_244_, v_inst_245_, v_aliases_246_, v_toBind_247_, v___f_248_, v_currNamespace_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_stx_262_){
_start:
{
lean_object* v_toApplicative_263_; lean_object* v_toBind_264_; lean_object* v_toPure_265_; lean_object* v_aliases_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_toApplicative_263_ = lean_ctor_get(v_inst_260_, 0);
v_toBind_264_ = lean_ctor_get(v_inst_260_, 1);
lean_inc(v_toBind_264_);
v_toPure_265_ = lean_ctor_get(v_toApplicative_263_, 1);
lean_inc(v_toPure_265_);
v_aliases_266_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_267_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_262_);
v___x_268_ = l_Lean_Syntax_isOfKind(v_stx_262_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_toBind_264_);
lean_dec(v_stx_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
v___x_269_ = lean_apply_2(v_toPure_265_, lean_box(0), v_aliases_266_);
return v___x_269_;
}
else
{
lean_object* v_getCurrNamespace_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_ids_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___x_277_; 
v_getCurrNamespace_270_ = lean_ctor_get(v_inst_261_, 0);
lean_inc(v_getCurrNamespace_270_);
lean_dec_ref(v_inst_261_);
lean_inc(v_toPure_265_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__1), 2, 1);
lean_closure_set(v___f_271_, 0, v_toPure_265_);
v___x_272_ = lean_unsigned_to_nat(3u);
v___x_273_ = l_Lean_Syntax_getArg(v_stx_262_, v___x_272_);
lean_dec(v_stx_262_);
v_ids_274_ = l_Lean_Syntax_getArgs(v___x_273_);
lean_dec(v___x_273_);
v___x_275_ = lean_box(v___x_268_);
lean_inc(v_toBind_264_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_276_, 0, v___x_275_);
lean_closure_set(v___f_276_, 1, v_toPure_265_);
lean_closure_set(v___f_276_, 2, v_ids_274_);
lean_closure_set(v___f_276_, 3, v_inst_260_);
lean_closure_set(v___f_276_, 4, v_aliases_266_);
lean_closure_set(v___f_276_, 5, v_toBind_264_);
lean_closure_set(v___f_276_, 6, v___f_271_);
v___x_277_ = lean_apply_4(v_toBind_264_, lean_box(0), lean_box(0), v_getCurrNamespace_270_, v___f_276_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax(lean_object* v_m_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_stx_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg(v_inst_279_, v_inst_280_, v_stx_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(lean_object* v_k_283_, uint8_t v_defValue_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_scopes_289_; lean_object* v___x_290_; lean_object* v_opts_291_; lean_object* v_map_292_; lean_object* v___x_293_; 
v___x_287_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_288_ = lean_st_ref_get(v___y_285_);
v_scopes_289_ = lean_ctor_get(v___x_288_, 2);
lean_inc(v_scopes_289_);
lean_dec(v___x_288_);
v___x_290_ = l_List_head_x21___redArg(v___x_287_, v_scopes_289_);
lean_dec(v_scopes_289_);
v_opts_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc_ref(v_opts_291_);
lean_dec(v___x_290_);
v_map_292_ = lean_ctor_get(v_opts_291_, 0);
lean_inc(v_map_292_);
lean_dec_ref(v_opts_291_);
v___x_293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_292_, v_k_283_);
lean_dec(v_map_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(v_defValue_284_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_309_; 
v_val_296_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_309_ == 0)
{
v___x_298_ = v___x_293_;
v_isShared_299_ = v_isSharedCheck_309_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_val_296_);
lean_dec(v___x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_309_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
if (lean_obj_tag(v_val_296_) == 1)
{
uint8_t v_v_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v_v_300_ = lean_ctor_get_uint8(v_val_296_, 0);
lean_dec_ref_known(v_val_296_, 0);
v___x_301_ = lean_box(v_v_300_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 0);
lean_ctor_set(v___x_298_, 0, v___x_301_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_307_; 
lean_dec(v_val_296_);
v___x_305_ = lean_box(v_defValue_284_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 0);
lean_ctor_set(v___x_298_, 0, v___x_305_);
v___x_307_ = v___x_298_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg___boxed(lean_object* v_k_310_, lean_object* v_defValue_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v_defValue_boxed_314_; lean_object* v_res_315_; 
v_defValue_boxed_314_ = lean_unbox(v_defValue_311_);
v_res_315_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v_k_310_, v_defValue_boxed_314_, v___y_312_);
lean_dec(v___y_312_);
lean_dec(v_k_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(lean_object* v_k_316_, uint8_t v_defValue_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v_k_316_, v_defValue_317_, v___y_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___boxed(lean_object* v_k_322_, lean_object* v_defValue_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_defValue_boxed_327_; lean_object* v_res_328_; 
v_defValue_boxed_327_ = lean_unbox(v_defValue_323_);
v_res_328_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3(v_k_322_, v_defValue_boxed_327_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v_k_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(lean_object* v_as_330_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; 
v___f_331_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8___closed__0));
v___x_332_ = l_List_eraseDupsBy___redArg(v___f_331_, v_as_330_);
return v___x_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
v___x_335_ = l_Lean_Syntax_isOfKind(v_x_333_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0___boxed(lean_object* v_x_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__0(v_x_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(uint8_t v___x_339_, lean_object* v___x_340_, lean_object* v_as_341_, size_t v_sz_342_, size_t v_i_343_, lean_object* v_b_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_lt(v_i_343_, v_sz_342_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v___x_340_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_b_344_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___y_352_; lean_object* v___x_360_; 
v_a_348_ = lean_array_uget_borrowed(v_as_341_, v_i_343_);
v___x_349_ = l_Lean_TSyntax_getId(v_a_348_);
v___x_350_ = 0;
v___x_360_ = l_Lean_Syntax_getRange_x3f(v_a_348_, v___x_350_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Syntax_instInhabitedRange_default;
v___y_352_ = v___x_361_;
goto v___jp_351_;
}
else
{
lean_object* v_val_362_; 
v_val_362_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v___x_360_, 1);
v___y_352_ = v_val_362_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; 
v___x_353_ = l_Lean_Syntax_ofRange(v___y_352_, v___x_339_);
lean_inc(v___x_340_);
v___x_354_ = l_Lean_Name_append(v___x_340_, v___x_349_);
v___x_355_ = l_Lean_mkIdentFrom(v___x_353_, v___x_354_, v___x_350_);
lean_dec(v___x_353_);
v___x_356_ = lean_array_push(v_b_344_, v___x_355_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_343_, v___x_357_);
v_i_343_ = v___x_358_;
v_b_344_ = v___x_356_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg___boxed(lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_as_365_, lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_b_368_, lean_object* v___y_369_){
_start:
{
uint8_t v___x_7742__boxed_370_; size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v___x_7742__boxed_370_ = lean_unbox(v___x_363_);
v_sz_boxed_371_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_372_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_7742__boxed_370_, v___x_364_, v_as_365_, v_sz_boxed_371_, v_i_boxed_372_, v_b_368_);
lean_dec_ref(v_as_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(lean_object* v_stx_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_aliases_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_aliases_378_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_379_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___redArg___closed__3));
lean_inc(v_stx_374_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_stx_374_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_stx_374_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_aliases_378_);
return v___x_381_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_ids_384_; lean_object* v___x_385_; 
v___x_382_ = lean_unsigned_to_nat(3u);
v___x_383_ = l_Lean_Syntax_getArg(v_stx_374_, v___x_382_);
lean_dec(v_stx_374_);
v_ids_384_ = l_Lean_Syntax_getArgs(v___x_383_);
lean_dec(v___x_383_);
v___x_385_ = l_Lean_Elab_Command_getScope___redArg(v___y_376_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_currNamespace_387_; size_t v_sz_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v_currNamespace_387_ = lean_ctor_get(v_a_386_, 2);
lean_inc(v_currNamespace_387_);
lean_dec(v_a_386_);
v_sz_388_ = lean_array_size(v_ids_384_);
v___x_389_ = ((size_t)0ULL);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_380_, v_currNamespace_387_, v_ids_384_, v_sz_388_, v___x_389_, v_aliases_378_);
lean_dec_ref(v_ids_384_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_390_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v_ids_384_);
v_a_407_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_385_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_385_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10___boxed(lean_object* v_stx_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(v_stx_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_419_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__0));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
if (lean_obj_tag(v_a_423_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = l_List_reverse___redArg(v_a_424_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_439_; 
v_head_426_ = lean_ctor_get(v_a_423_, 0);
v_tail_427_ = lean_ctor_get(v_a_423_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_423_);
if (v_isSharedCheck_439_ == 0)
{
v___x_429_ = v_a_423_;
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_tail_427_);
lean_inc(v_head_426_);
lean_dec(v_a_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_439_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_431_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1, &l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5___closed__1);
v___x_432_ = l_Lean_MessageData_ofName(v_head_426_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_431_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_a_424_);
lean_ctor_set(v___x_429_, 0, v___x_434_);
v___x_436_ = v___x_429_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_424_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_a_423_ = v_tail_427_;
v_a_424_ = v___x_436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
if (lean_obj_tag(v_a_440_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_array_to_list(v_a_441_);
return v___x_442_;
}
else
{
lean_object* v_head_443_; lean_object* v_tail_444_; lean_object* v_fst_445_; lean_object* v_snd_446_; uint8_t v___x_447_; 
v_head_443_ = lean_ctor_get(v_a_440_, 0);
lean_inc(v_head_443_);
v_tail_444_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_tail_444_);
lean_dec_ref_known(v_a_440_, 2);
v_fst_445_ = lean_ctor_get(v_head_443_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v_head_443_, 1);
lean_inc(v_snd_446_);
lean_dec(v_head_443_);
v___x_447_ = lean_name_eq(v_fst_445_, v_snd_446_);
lean_dec(v_snd_446_);
if (v___x_447_ == 0)
{
lean_dec(v_fst_445_);
v_a_440_ = v_tail_444_;
goto _start;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_array_push(v_a_441_, v_fst_445_);
v_a_440_ = v_tail_444_;
v_a_441_ = v___x_449_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(lean_object* v_opts_451_, lean_object* v_opt_452_){
_start:
{
lean_object* v_name_453_; lean_object* v_defValue_454_; lean_object* v_map_455_; lean_object* v___x_456_; 
v_name_453_ = lean_ctor_get(v_opt_452_, 0);
v_defValue_454_ = lean_ctor_get(v_opt_452_, 1);
v_map_455_ = lean_ctor_get(v_opts_451_, 0);
v___x_456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_455_, v_name_453_);
if (lean_obj_tag(v___x_456_) == 0)
{
uint8_t v___x_457_; 
v___x_457_ = lean_unbox(v_defValue_454_);
return v___x_457_;
}
else
{
lean_object* v_val_458_; 
v_val_458_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_458_);
lean_dec_ref_known(v___x_456_, 1);
if (lean_obj_tag(v_val_458_) == 1)
{
uint8_t v_v_459_; 
v_v_459_ = lean_ctor_get_uint8(v_val_458_, 0);
lean_dec_ref_known(v_val_458_, 0);
return v_v_459_;
}
else
{
uint8_t v___x_460_; 
lean_dec(v_val_458_);
v___x_460_ = lean_unbox(v_defValue_454_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15___boxed(lean_object* v_opts_461_, lean_object* v_opt_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(v_opts_461_, v_opt_462_);
lean_dec_ref(v_opt_462_);
lean_dec_ref(v_opts_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0(uint8_t v_suppressElabErrors_466_, uint8_t v___y_467_, lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 1)
{
lean_object* v_pre_469_; 
v_pre_469_ = lean_ctor_get(v_x_468_, 0);
if (lean_obj_tag(v_pre_469_) == 0)
{
lean_object* v_str_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_str_470_ = lean_ctor_get(v_x_468_, 1);
v___x_471_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___closed__0));
v___x_472_ = lean_string_dec_eq(v_str_470_, v___x_471_);
if (v___x_472_ == 0)
{
return v___x_472_;
}
else
{
return v_suppressElabErrors_466_;
}
}
else
{
return v___y_467_;
}
}
else
{
return v___y_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___boxed(lean_object* v_suppressElabErrors_473_, lean_object* v___y_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_suppressElabErrors_boxed_476_; uint8_t v___y_7950__boxed_477_; uint8_t v_res_478_; lean_object* v_r_479_; 
v_suppressElabErrors_boxed_476_ = lean_unbox(v_suppressElabErrors_473_);
v___y_7950__boxed_477_ = lean_unbox(v___y_474_);
v_res_478_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0(v_suppressElabErrors_boxed_476_, v___y_7950__boxed_477_, v_x_475_);
lean_dec(v_x_475_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_480_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__0);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_484_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
lean_ctor_set(v___x_486_, 3, v___x_485_);
lean_ctor_set(v___x_486_, 4, v___x_484_);
lean_ctor_set(v___x_486_, 5, v___x_484_);
lean_ctor_set(v___x_486_, 6, v___x_484_);
lean_ctor_set(v___x_486_, 7, v___x_484_);
lean_ctor_set(v___x_486_, 8, v___x_484_);
lean_ctor_set(v___x_486_, 9, v___x_484_);
lean_ctor_set(v___x_486_, 10, v___x_484_);
lean_ctor_set(v___x_486_, 11, v___x_483_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(32u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4(void){
_start:
{
size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_490_ = ((size_t)5ULL);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_unsigned_to_nat(32u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__3);
v___x_495_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_491_);
lean_ctor_set(v___x_495_, 3, v___x_491_);
lean_ctor_set_usize(v___x_495_, 4, v___x_490_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_496_ = lean_box(1);
v___x_497_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__4);
v___x_498_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__1);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_msgData_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_env_504_; uint8_t v___x_505_; lean_object* v_env_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_scopes_509_; lean_object* v___x_510_; lean_object* v_opts_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_503_ = lean_st_ref_get(v___y_501_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc_ref(v_env_504_);
lean_dec(v___x_503_);
v___x_505_ = 0;
v_env_506_ = l_Lean_Environment_setRecordingDeps(v_env_504_, v___x_505_);
v___x_507_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_508_ = lean_st_ref_get(v___y_501_);
v_scopes_509_ = lean_ctor_get(v___x_508_, 2);
lean_inc(v_scopes_509_);
lean_dec(v___x_508_);
v___x_510_ = l_List_head_x21___redArg(v___x_507_, v_scopes_509_);
lean_dec(v_scopes_509_);
v_opts_511_ = lean_ctor_get(v___x_510_, 1);
lean_inc_ref(v_opts_511_);
lean_dec(v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__2);
v___x_513_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___closed__5);
v___x_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_514_, 0, v_env_506_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
lean_ctor_set(v___x_514_, 3, v_opts_511_);
v___x_515_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_msgData_500_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_msgData_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v_msgData_517_, v___y_518_);
lean_dec(v___y_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(lean_object* v_ref_522_, lean_object* v_msgData_523_, uint8_t v_severity_524_, uint8_t v_isSilent_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___y_530_; uint8_t v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_595_; uint8_t v___y_596_; uint8_t v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_623_; lean_object* v___y_624_; uint8_t v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; uint8_t v___y_631_; uint8_t v___y_632_; uint8_t v___y_633_; uint8_t v___x_648_; uint8_t v___y_650_; uint8_t v___y_651_; uint8_t v___y_652_; uint8_t v___y_654_; uint8_t v___x_666_; 
v___x_648_ = 2;
v___x_666_ = l_Lean_instBEqMessageSeverity_beq(v_severity_524_, v___x_648_);
if (v___x_666_ == 0)
{
v___y_654_ = v___x_666_;
goto v___jp_653_;
}
else
{
uint8_t v___x_667_; 
lean_inc_ref(v_msgData_523_);
v___x_667_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_523_);
v___y_654_ = v___x_667_;
goto v___jp_653_;
}
v___jp_529_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Elab_Command_getScope___redArg(v___y_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_currNamespace_540_; lean_object* v___x_541_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v_currNamespace_540_ = lean_ctor_get(v_a_539_, 2);
lean_inc(v_currNamespace_540_);
lean_dec(v_a_539_);
v___x_541_ = l_Lean_Elab_Command_getScope___redArg(v___y_537_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_577_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_577_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_577_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_577_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_openDecls_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_env_551_; lean_object* v_messages_552_; lean_object* v_scopes_553_; lean_object* v_usedQuotCtxts_554_; lean_object* v_nextMacroScope_555_; lean_object* v_maxRecDepth_556_; lean_object* v_ngen_557_; lean_object* v_auxDeclNGen_558_; lean_object* v_infoState_559_; lean_object* v_traceState_560_; lean_object* v_snapshotTasks_561_; lean_object* v_prevLinterStates_562_; lean_object* v_codeQualityEntryTasks_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_576_; 
v_openDecls_546_ = lean_ctor_get(v_a_542_, 3);
lean_inc(v_openDecls_546_);
lean_dec(v_a_542_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_currNamespace_540_);
lean_ctor_set(v___x_547_, 1, v_openDecls_546_);
v___x_548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___y_530_);
lean_inc_ref(v___y_534_);
lean_inc_ref(v___y_533_);
v___x_549_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_549_, 0, v___y_533_);
lean_ctor_set(v___x_549_, 1, v___y_536_);
lean_ctor_set(v___x_549_, 2, v___y_535_);
lean_ctor_set(v___x_549_, 3, v___y_534_);
lean_ctor_set(v___x_549_, 4, v___x_548_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5, v___y_531_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5 + 1, v___y_532_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5 + 2, v_isSilent_525_);
v___x_550_ = lean_st_ref_take(v___y_537_);
v_env_551_ = lean_ctor_get(v___x_550_, 0);
v_messages_552_ = lean_ctor_get(v___x_550_, 1);
v_scopes_553_ = lean_ctor_get(v___x_550_, 2);
v_usedQuotCtxts_554_ = lean_ctor_get(v___x_550_, 3);
v_nextMacroScope_555_ = lean_ctor_get(v___x_550_, 4);
v_maxRecDepth_556_ = lean_ctor_get(v___x_550_, 5);
v_ngen_557_ = lean_ctor_get(v___x_550_, 6);
v_auxDeclNGen_558_ = lean_ctor_get(v___x_550_, 7);
v_infoState_559_ = lean_ctor_get(v___x_550_, 8);
v_traceState_560_ = lean_ctor_get(v___x_550_, 9);
v_snapshotTasks_561_ = lean_ctor_get(v___x_550_, 10);
v_prevLinterStates_562_ = lean_ctor_get(v___x_550_, 11);
v_codeQualityEntryTasks_563_ = lean_ctor_get(v___x_550_, 12);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_576_ == 0)
{
v___x_565_ = v___x_550_;
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_codeQualityEntryTasks_563_);
lean_inc(v_prevLinterStates_562_);
lean_inc(v_snapshotTasks_561_);
lean_inc(v_traceState_560_);
lean_inc(v_infoState_559_);
lean_inc(v_auxDeclNGen_558_);
lean_inc(v_ngen_557_);
lean_inc(v_maxRecDepth_556_);
lean_inc(v_nextMacroScope_555_);
lean_inc(v_usedQuotCtxts_554_);
lean_inc(v_scopes_553_);
lean_inc(v_messages_552_);
lean_inc(v_env_551_);
lean_dec(v___x_550_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Lean_MessageLog_add(v___x_549_, v_messages_552_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_env_551_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_scopes_553_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_usedQuotCtxts_554_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_nextMacroScope_555_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v_maxRecDepth_556_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_ngen_557_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_auxDeclNGen_558_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_575_, 9, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 10, v_snapshotTasks_561_);
lean_ctor_set(v_reuseFailAlloc_575_, 11, v_prevLinterStates_562_);
lean_ctor_set(v_reuseFailAlloc_575_, 12, v_codeQualityEntryTasks_563_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_st_ref_put(v___y_537_, v___x_570_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_567_);
v___x_573_ = v___x_544_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_567_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_currNamespace_540_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_530_);
v_a_578_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_541_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_541_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_530_);
v_a_586_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_538_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_538_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
v___jp_594_:
{
lean_object* v_fileName_600_; lean_object* v_fileMap_601_; uint8_t v_suppressElabErrors_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_621_; 
v_fileName_600_ = lean_ctor_get(v___y_526_, 0);
v_fileMap_601_ = lean_ctor_get(v___y_526_, 1);
v_suppressElabErrors_602_ = lean_ctor_get_uint8(v___y_526_, sizeof(void*)*10);
v___x_603_ = lean_box(v_suppressElabErrors_602_);
v___x_604_ = lean_box(v___y_595_);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___lam__0___boxed), 3, 2);
lean_closure_set(v___f_605_, 0, v___x_603_);
lean_closure_set(v___f_605_, 1, v___x_604_);
v___x_606_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_523_);
v___x_607_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v___x_606_, v___y_527_);
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_621_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_621_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_621_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc_ref_n(v_fileMap_601_, 2);
v___x_612_ = l_Lean_FileMap_toPosition(v_fileMap_601_, v___y_598_);
lean_dec(v___y_598_);
v___x_613_ = l_Lean_FileMap_toPosition(v_fileMap_601_, v___y_599_);
lean_dec(v___y_599_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___closed__0));
if (v_suppressElabErrors_602_ == 0)
{
lean_del_object(v___x_610_);
lean_dec_ref(v___f_605_);
v___y_530_ = v_a_608_;
v___y_531_ = v___y_596_;
v___y_532_ = v___y_597_;
v___y_533_ = v_fileName_600_;
v___y_534_ = v___x_615_;
v___y_535_ = v___x_614_;
v___y_536_ = v___x_612_;
v___y_537_ = v___y_527_;
goto v___jp_529_;
}
else
{
uint8_t v___x_616_; 
lean_inc(v_a_608_);
v___x_616_ = l_Lean_MessageData_hasTag(v___f_605_, v_a_608_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_619_; 
lean_dec_ref_known(v___x_614_, 1);
lean_dec_ref(v___x_612_);
lean_dec(v_a_608_);
v___x_617_ = lean_box(0);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_617_);
v___x_619_ = v___x_610_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_del_object(v___x_610_);
v___y_530_ = v_a_608_;
v___y_531_ = v___y_596_;
v___y_532_ = v___y_597_;
v___y_533_ = v_fileName_600_;
v___y_534_ = v___x_615_;
v___y_535_ = v___x_614_;
v___y_536_ = v___x_612_;
v___y_537_ = v___y_527_;
goto v___jp_529_;
}
}
}
}
v___jp_622_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Syntax_getTailPos_x3f(v___y_624_, v___y_625_);
lean_dec(v___y_624_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_inc(v___y_627_);
v___y_595_ = v___y_623_;
v___y_596_ = v___y_625_;
v___y_597_ = v___y_626_;
v___y_598_ = v___y_627_;
v___y_599_ = v___y_627_;
goto v___jp_594_;
}
else
{
lean_object* v_val_629_; 
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_628_, 1);
v___y_595_ = v___y_623_;
v___y_596_ = v___y_625_;
v___y_597_ = v___y_626_;
v___y_598_ = v___y_627_;
v___y_599_ = v_val_629_;
goto v___jp_594_;
}
}
v___jp_630_:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Elab_Command_getRef___redArg(v___y_526_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v_ref_636_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v_ref_636_ = l_Lean_replaceRef(v_ref_522_, v_a_635_);
lean_dec(v_a_635_);
v___x_637_ = l_Lean_Syntax_getPos_x3f(v_ref_636_, v___y_632_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___y_623_ = v___y_631_;
v___y_624_ = v_ref_636_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_633_;
v___y_627_ = v___x_638_;
goto v___jp_622_;
}
else
{
lean_object* v_val_639_; 
v_val_639_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v___x_637_, 1);
v___y_623_ = v___y_631_;
v___y_624_ = v_ref_636_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_633_;
v___y_627_ = v_val_639_;
goto v___jp_622_;
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_msgData_523_);
v_a_640_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_634_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_634_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
v___jp_649_:
{
if (v___y_652_ == 0)
{
v___y_631_ = v___y_650_;
v___y_632_ = v___y_651_;
v___y_633_ = v_severity_524_;
goto v___jp_630_;
}
else
{
v___y_631_ = v___y_650_;
v___y_632_ = v___y_651_;
v___y_633_ = v___x_648_;
goto v___jp_630_;
}
}
v___jp_653_:
{
if (v___y_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_scopes_657_; lean_object* v___x_658_; lean_object* v_opts_659_; uint8_t v___x_660_; uint8_t v___x_661_; 
v___x_655_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_656_ = lean_st_ref_get(v___y_527_);
v_scopes_657_ = lean_ctor_get(v___x_656_, 2);
lean_inc(v_scopes_657_);
lean_dec(v___x_656_);
v___x_658_ = l_List_head_x21___redArg(v___x_655_, v_scopes_657_);
lean_dec(v_scopes_657_);
v_opts_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc_ref(v_opts_659_);
lean_dec(v___x_658_);
v___x_660_ = 1;
v___x_661_ = l_Lean_instBEqMessageSeverity_beq(v_severity_524_, v___x_660_);
if (v___x_661_ == 0)
{
lean_dec_ref(v_opts_659_);
v___y_650_ = v___y_654_;
v___y_651_ = v___y_654_;
v___y_652_ = v___x_661_;
goto v___jp_649_;
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = l_Lean_warningAsError;
v___x_663_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__15(v_opts_659_, v___x_662_);
lean_dec_ref(v_opts_659_);
v___y_650_ = v___y_654_;
v___y_651_ = v___y_654_;
v___y_652_ = v___x_663_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v_msgData_523_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8___boxed(lean_object* v_ref_668_, lean_object* v_msgData_669_, lean_object* v_severity_670_, lean_object* v_isSilent_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_severity_boxed_675_; uint8_t v_isSilent_boxed_676_; lean_object* v_res_677_; 
v_severity_boxed_675_ = lean_unbox(v_severity_670_);
v_isSilent_boxed_676_ = lean_unbox(v_isSilent_671_);
v_res_677_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(v_ref_668_, v_msgData_669_, v_severity_boxed_675_, v_isSilent_boxed_676_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v_ref_668_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(lean_object* v_ref_678_, lean_object* v_msgData_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = 1;
v___x_684_ = 0;
v___x_685_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8(v_ref_678_, v_msgData_679_, v___x_683_, v___x_684_, v___y_680_, v___y_681_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6___boxed(lean_object* v_ref_686_, lean_object* v_msgData_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(v_ref_686_, v_msgData_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_ref_686_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__0));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__2));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(lean_object* v_linterOption_698_, lean_object* v_stx_699_, lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_name_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_722_; 
v_name_704_ = lean_ctor_get(v_linterOption_698_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_linterOption_698_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_linterOption_698_, 1);
lean_dec(v_unused_723_);
v___x_706_ = v_linterOption_698_;
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_name_704_);
lean_dec(v_linterOption_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_722_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__1);
lean_inc(v_name_704_);
v___x_709_ = l_Lean_MessageData_ofName(v_name_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 7);
lean_ctor_set(v___x_706_, 1, v___x_709_);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_721_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_disable_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_712_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___closed__3);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v_disable_714_ = l_Lean_MessageData_note(v___x_713_);
v___x_715_ = l_Lean_Linter_linterMessageTag;
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v_msg_700_);
lean_ctor_set(v___x_716_, 1, v_disable_714_);
v___x_717_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_718_, 0, v_name_704_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
lean_inc(v_stx_699_);
v___x_719_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_719_, 0, v_stx_699_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6(v_stx_699_, v___x_719_, v___y_701_, v___y_702_);
lean_dec(v_stx_699_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4___boxed(lean_object* v_linterOption_724_, lean_object* v_stx_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v_linterOption_724_, v_stx_725_, v_msg_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(lean_object* v_comp_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
if (lean_obj_tag(v_a_732_) == 0)
{
return v_a_733_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; uint8_t v___x_736_; 
v_head_734_ = lean_ctor_get(v_a_732_, 0);
v_tail_735_ = lean_ctor_get(v_a_732_, 1);
v___x_736_ = lean_name_eq(v_head_734_, v_comp_731_);
if (v___x_736_ == 0)
{
v_a_732_ = v_tail_735_;
goto _start;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_a_733_, v___x_738_);
lean_dec(v_a_733_);
v_a_732_ = v_tail_735_;
v_a_733_ = v___x_739_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2___boxed(lean_object* v_comp_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_comp_741_, v_a_742_, v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_comp_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(lean_object* v___x_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
if (lean_obj_tag(v_a_746_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = l_List_reverse___redArg(v_a_747_);
return v___x_748_;
}
else
{
lean_object* v_head_749_; lean_object* v_tail_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_763_; 
v_head_749_ = lean_ctor_get(v_a_746_, 0);
v_tail_750_ = lean_ctor_get(v_a_746_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_a_746_);
if (v_isSharedCheck_763_ == 0)
{
v___x_752_ = v_a_746_;
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_tail_750_);
lean_inc(v_head_749_);
lean_dec(v_a_746_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_763_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = l_List_countP_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__2(v_head_749_, v___x_745_, v___x_755_);
v___x_757_ = lean_nat_dec_lt(v___x_754_, v___x_756_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_del_object(v___x_752_);
lean_dec(v_head_749_);
v_a_746_ = v_tail_750_;
goto _start;
}
else
{
lean_object* v___x_760_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v_a_747_);
v___x_760_ = v___x_752_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_head_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_747_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
v_a_746_ = v_tail_750_;
v_a_747_ = v___x_760_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7___boxed(lean_object* v___x_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_764_, v_a_765_, v_a_766_);
lean_dec(v___x_764_);
return v_res_767_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__0));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__2));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__4));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__6));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__8));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(uint8_t v___x_785_, lean_object* v_as_786_, size_t v_sz_787_, size_t v_i_788_, lean_object* v_b_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_a_794_; uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_lt(v_i_788_, v_sz_787_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_789_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v_a_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_800_ = lean_box(0);
v_a_801_ = lean_array_uget_borrowed(v_as_786_, v_i_788_);
v___x_802_ = l_Lean_Syntax_getId(v_a_801_);
v___x_803_ = l_Lean_Name_hasMacroScopes(v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = l_Lean_isPrivateName(v___x_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
lean_inc(v___x_802_);
v___x_806_ = l_Lean_Name_components(v___x_802_);
v___x_807_ = ((lean_object*)(l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_DupNamespace_8692490____hygCtx___hyg_4_));
v___x_808_ = l_Lean_getBoolOption___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__3___redArg(v___x_807_, v___x_785_, v___y_791_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___y_811_; lean_object* v___y_844_; uint8_t v___x_848_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_848_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
lean_inc(v___x_806_);
v___x_850_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__7(v___x_806_, v___x_806_, v___x_849_);
lean_dec(v___x_806_);
v___x_851_ = l_List_eraseDups___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__8(v___x_850_);
v___y_811_ = v___x_851_;
goto v___jp_810_;
}
else
{
if (lean_obj_tag(v___x_806_) == 0)
{
v___y_844_ = v___x_806_;
goto v___jp_843_;
}
else
{
lean_object* v_tail_852_; 
v_tail_852_ = lean_ctor_get(v___x_806_, 1);
lean_inc(v_tail_852_);
v___y_844_ = v_tail_852_;
goto v___jp_843_;
}
}
v___jp_810_:
{
if (lean_obj_tag(v___y_811_) == 0)
{
lean_dec(v___x_802_);
v_a_794_ = v___x_800_;
goto v___jp_793_;
}
else
{
lean_object* v_tail_812_; 
v_tail_812_ = lean_ctor_get(v___y_811_, 1);
if (lean_obj_tag(v_tail_812_) == 0)
{
lean_object* v_head_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_829_; 
v_head_813_ = lean_ctor_get(v___y_811_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___y_811_, 1);
lean_dec(v_unused_830_);
v___x_815_ = v___y_811_;
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_head_813_);
lean_dec(v___y_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_829_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__1);
v___x_818_ = l_Lean_MessageData_ofName(v_head_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 7);
lean_ctor_set(v___x_815_, 1, v___x_818_);
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_828_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__3);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_MessageData_ofConstName(v___x_802_, v___x_785_);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
lean_inc(v_a_801_);
v___x_827_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_805_, v_a_801_, v___x_826_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref_known(v___x_827_, 1);
v_a_794_ = v___x_800_;
goto v___jp_793_;
}
else
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_831_ = lean_box(0);
v___x_832_ = l_List_mapTR_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__5(v___y_811_, v___x_831_);
v___x_833_ = l_Lean_MessageData_andList(v___x_832_);
v___x_834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__7);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
v___x_836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__9);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_MessageData_ofConstName(v___x_802_, v___x_785_);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__5);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
lean_inc(v_a_801_);
v___x_842_ = l_Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4(v___x_805_, v_a_801_, v___x_841_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref_known(v___x_842_, 1);
v_a_794_ = v___x_800_;
goto v___jp_793_;
}
else
{
return v___x_842_;
}
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v___x_806_, v___y_844_);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___closed__10));
v___x_847_ = l_List_filterMapTR_go___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__6(v___x_845_, v___x_846_);
v___y_811_ = v___x_847_;
goto v___jp_810_;
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v___x_806_);
lean_dec(v___x_802_);
v_a_853_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_808_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_808_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_dec(v___x_802_);
v_a_794_ = v___x_800_;
goto v___jp_793_;
}
}
else
{
lean_dec(v___x_802_);
v_a_794_ = v___x_800_;
goto v___jp_793_;
}
}
v___jp_793_:
{
size_t v___x_795_; size_t v___x_796_; 
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_788_, v___x_795_);
v_i_788_ = v___x_796_;
v_b_789_ = v_a_794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9___boxed(lean_object* v___x_861_, lean_object* v_as_862_, lean_object* v_sz_863_, lean_object* v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_8509__boxed_869_; size_t v_sz_boxed_870_; size_t v_i_boxed_871_; lean_object* v_res_872_; 
v___x_8509__boxed_869_ = lean_unbox(v___x_861_);
v_sz_boxed_870_ = lean_unbox_usize(v_sz_863_);
lean_dec(v_sz_863_);
v_i_boxed_871_ = lean_unbox_usize(v_i_864_);
lean_dec(v_i_864_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_8509__boxed_869_, v_as_862_, v_sz_boxed_870_, v_i_boxed_871_, v_b_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v_as_862_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(lean_object* v___x_873_, lean_object* v_pos_874_, lean_object* v_init_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_d_879_; 
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v_l_884_; lean_object* v_r_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v_a_888_; 
v_k_882_ = lean_ctor_get(v_x_876_, 1);
lean_inc(v_k_882_);
v_v_883_ = lean_ctor_get(v_x_876_, 2);
lean_inc(v_v_883_);
v_l_884_ = lean_ctor_get(v_x_876_, 3);
lean_inc(v_l_884_);
v_r_885_ = lean_ctor_get(v_x_876_, 4);
lean_inc(v_r_885_);
lean_dec_ref_known(v_x_876_, 5);
v___x_886_ = 0;
v___x_887_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_873_, v_pos_874_, v_init_875_, v_l_884_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v_a_889_; 
lean_inc_ref(v_a_888_);
lean_dec_ref(v___x_887_);
lean_dec(v_r_885_);
lean_dec(v_v_883_);
lean_dec(v_k_882_);
v_a_889_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v_a_888_, 1);
v_d_879_ = v_a_889_;
goto v___jp_878_;
}
else
{
lean_object* v_range_890_; lean_object* v_a_891_; lean_object* v_selectionRange_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_914_; 
v_range_890_ = lean_ctor_get(v_v_883_, 0);
lean_inc_ref(v_range_890_);
v_a_891_ = lean_ctor_get(v_a_888_, 0);
v_selectionRange_892_ = lean_ctor_get(v_v_883_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_v_883_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_v_883_, 0);
lean_dec(v_unused_915_);
v___x_894_ = v_v_883_;
v_isShared_895_ = v_isSharedCheck_914_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_selectionRange_892_);
lean_dec(v_v_883_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_914_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_pos_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_pos_896_ = lean_ctor_get(v_range_890_, 0);
lean_inc_ref(v_pos_896_);
lean_dec_ref(v_range_890_);
v___x_897_ = l_Lean_FileMap_ofPosition(v___x_873_, v_pos_896_);
v___x_898_ = lean_nat_dec_le(v_pos_874_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v_a_899_; 
lean_del_object(v___x_894_);
lean_dec_ref(v_selectionRange_892_);
lean_dec(v_k_882_);
v_a_899_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_887_);
if (lean_obj_tag(v_a_899_) == 0)
{
lean_object* v_a_900_; 
lean_dec(v_r_885_);
v_a_900_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v_a_899_, 1);
v_d_879_ = v_a_900_;
goto v___jp_878_;
}
else
{
lean_object* v_a_901_; 
v_a_901_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v_a_899_, 1);
v_init_875_ = v_a_901_;
v_x_876_ = v_r_885_;
goto _start;
}
}
else
{
lean_object* v_pos_903_; lean_object* v_endPos_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_inc(v_a_891_);
lean_dec_ref(v___x_887_);
v_pos_903_ = lean_ctor_get(v_selectionRange_892_, 0);
lean_inc_ref(v_pos_903_);
v_endPos_904_ = lean_ctor_get(v_selectionRange_892_, 2);
lean_inc_ref(v_endPos_904_);
lean_dec_ref(v_selectionRange_892_);
v___x_905_ = l_Lean_FileMap_ofPosition(v___x_873_, v_pos_903_);
v___x_906_ = l_Lean_FileMap_ofPosition(v___x_873_, v_endPos_904_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_906_);
lean_ctor_set(v___x_894_, 0, v___x_905_);
v___x_908_ = v___x_894_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_906_);
v___x_908_ = v_reuseFailAlloc_913_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_Syntax_ofRange(v___x_908_, v___x_898_);
v___x_910_ = l_Lean_mkIdentFrom(v___x_909_, v_k_882_, v___x_886_);
lean_dec(v___x_909_);
v___x_911_ = lean_array_push(v_a_891_, v___x_910_);
v_init_875_ = v___x_911_;
v_x_876_ = v_r_885_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_init_875_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_d_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg___boxed(lean_object* v___x_918_, lean_object* v_pos_919_, lean_object* v_init_920_, lean_object* v_x_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_918_, v_pos_919_, v_init_920_, v_x_921_);
lean_dec(v_pos_919_);
lean_dec_ref(v___x_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(lean_object* v_pos_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_env_930_; lean_object* v_fileMap_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v_drs_936_; lean_object* v_nms_937_; lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v___x_928_ = lean_box(1);
v___x_929_ = lean_st_ref_get(v___y_926_);
v_env_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc_ref(v_env_930_);
lean_dec(v___x_929_);
v_fileMap_931_ = lean_ctor_get(v___y_925_, 1);
v___x_932_ = l_Lean_declRangeExt;
v___x_933_ = lean_box(1);
v___x_934_ = lean_box(0);
v___x_935_ = 0;
v_drs_936_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_928_, v___x_932_, v_env_930_, v___x_933_, v___x_934_, v___x_935_);
v_nms_937_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v___x_938_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v_fileMap_931_, v_pos_924_, v_nms_937_, v_drs_936_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_a_943_; lean_object* v___x_945_; 
v_a_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_a_943_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_a_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_943_);
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
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1___boxed(lean_object* v_pos_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v_pos_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v_pos_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(lean_object* v_o_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v___x_959_; lean_object* v_toEnvExtension_960_; lean_object* v_asyncMode_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v_merged_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
v___x_956_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_957_ = lean_st_ref_get(v___y_954_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v___x_959_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_960_ = lean_ctor_get(v___x_959_, 0);
v_asyncMode_961_ = lean_ctor_get(v_toEnvExtension_960_, 2);
v___x_962_ = lean_box(0);
v___x_963_ = 0;
v___x_964_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_956_, v___x_959_, v_env_958_, v_asyncMode_961_, v___x_962_, v___x_963_);
v_merged_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_964_, 1);
lean_dec(v_unused_974_);
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_merged_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_merged_965_);
lean_ctor_set(v___x_967_, 0, v_o_953_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_o_953_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_merged_965_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg___boxed(lean_object* v_o_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_975_, v___y_976_);
lean_dec(v___y_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_scopes_984_; lean_object* v___x_985_; lean_object* v_opts_986_; lean_object* v___x_987_; 
v___x_982_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_983_ = lean_st_ref_get(v___y_980_);
v_scopes_984_ = lean_ctor_get(v___x_983_, 2);
lean_inc(v_scopes_984_);
lean_dec(v___x_983_);
v___x_985_ = l_List_head_x21___redArg(v___x_982_, v_scopes_984_);
lean_dec(v_scopes_984_);
v_opts_986_ = lean_ctor_get(v___x_985_, 1);
lean_inc_ref(v_opts_986_);
lean_dec(v___x_985_);
v___x_987_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_opts_986_, v___y_980_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0___boxed(lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(lean_object* v___f_992_, lean_object* v_stx_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1057_; 
v___x_997_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0(v___y_994_, v___y_995_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1057_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1057_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v_aliases_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; 
v___x_1002_ = l_Lean_Linter_Extra_linter_extra_dupNamespace;
v___x_1003_ = l_Lean_Linter_getLinterValue(v___x_1002_, v_a_998_);
lean_dec(v_a_998_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_dec(v_stx_993_);
lean_dec_ref(v___f_992_);
v___x_1040_ = lean_box(0);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1040_);
v___x_1042_ = v___x_1000_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1044_; 
lean_del_object(v___x_1000_);
lean_inc(v_stx_993_);
v___x_1044_ = l_Lean_Syntax_find_x3f(v_stx_993_, v___f_992_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10(v_val_1045_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_aliases_1033_ = v_a_1047_;
v___y_1034_ = v___y_994_;
v___y_1035_ = v___y_995_;
goto v___jp_1032_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_stx_993_);
v_a_1048_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1046_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1044_);
v___x_1056_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___redArg___lam__3___closed__0));
v_aliases_1033_ = v___x_1056_;
v___y_1034_ = v___y_994_;
v___y_1035_ = v___y_995_;
goto v___jp_1032_;
}
}
v___jp_1004_:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1(v___y_1008_, v___y_1007_, v___y_1006_);
lean_dec(v___y_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; size_t v_sz_1013_; size_t v___x_1014_; lean_object* v___x_1015_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = l_Array_append___redArg(v_a_1010_, v___y_1005_);
lean_dec_ref(v___y_1005_);
v___x_1012_ = lean_box(0);
v_sz_1013_ = lean_array_size(v___x_1011_);
v___x_1014_ = ((size_t)0ULL);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__9(v___x_1003_, v___x_1011_, v_sz_1013_, v___x_1014_, v___x_1012_, v___y_1007_, v___y_1006_);
lean_dec_ref(v___x_1011_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1015_, 0);
lean_dec(v_unused_1023_);
v___x_1017_ = v___x_1015_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1015_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1012_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1012_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
return v___x_1015_;
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v___y_1005_);
v_a_1024_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1009_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1009_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
v___jp_1032_:
{
uint8_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = 0;
v___x_1037_ = l_Lean_Syntax_getPos_x3f(v_stx_993_, v___x_1036_);
lean_dec(v_stx_993_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_unsigned_to_nat(0u);
v___y_1005_ = v_aliases_1033_;
v___y_1006_ = v___y_1035_;
v___y_1007_ = v___y_1034_;
v___y_1008_ = v___x_1038_;
goto v___jp_1004_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v___x_1037_, 1);
v___y_1005_ = v_aliases_1033_;
v___y_1006_ = v___y_1035_;
v___y_1007_ = v___y_1034_;
v___y_1008_ = v_val_1039_;
goto v___jp_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1___boxed(lean_object* v___f_1058_, lean_object* v_stx_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace___lam__1(v___f_1058_, v_stx_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(lean_object* v_o_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___redArg(v_o_1080_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0___boxed(lean_object* v_o_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__0_spec__0(v_o_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(lean_object* v___x_1090_, lean_object* v_pos_1091_, lean_object* v_init_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___redArg(v___x_1090_, v_pos_1091_, v_init_1092_, v_x_1093_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2___boxed(lean_object* v___x_1098_, lean_object* v_pos_1099_, lean_object* v_init_1100_, lean_object* v_x_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_Extra_DupNamespaceLinter_getNamesFrom___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__1_spec__2(v___x_1098_, v_pos_1099_, v_init_1100_, v_x_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v_pos_1099_);
lean_dec_ref(v___x_1098_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(uint8_t v___x_1106_, lean_object* v___x_1107_, lean_object* v_as_1108_, size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___redArg(v___x_1106_, v___x_1107_, v_as_1108_, v_sz_1109_, v_i_1110_, v_b_1111_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13___boxed(lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v_as_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_9071__boxed_1125_; size_t v_sz_boxed_1126_; size_t v_i_boxed_1127_; lean_object* v_res_1128_; 
v___x_9071__boxed_1125_ = lean_unbox(v___x_1116_);
v_sz_boxed_1126_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1127_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_Extra_DupNamespaceLinter_getAliasSyntax___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__10_spec__13(v___x_9071__boxed_1125_, v___x_1117_, v_as_1118_, v_sz_boxed_1126_, v_i_boxed_1127_, v_b_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v_as_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14(lean_object* v_msgData_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___redArg(v_msgData_1129_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14___boxed(lean_object* v_msgData_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_Extra_DupNamespaceLinter_dupNamespace_spec__4_spec__6_spec__8_spec__14(v_msgData_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Linter_Extra_DupNamespaceLinter_dupNamespace));
v___x_1141_ = l_Lean_Elab_Command_addLinter(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2____boxed(lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Linter_Extra_DupNamespace_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_DupNamespace_528843787____hygCtx___hyg_2_();
return v_res_1143_;
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
