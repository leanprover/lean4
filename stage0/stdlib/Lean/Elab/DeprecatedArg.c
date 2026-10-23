// Lean compiler output
// Module: Lean.Elab.DeprecatedArg
// Imports: public import Lean.EnvExtension public import Lean.Message import Lean.Elab.Term import Lean.Linter.Deprecated
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_mkSinceHint(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(34, 76, 221, 236, 220, 4, 80, 27)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "if true, generate deprecation warnings and errors for deprecated parameters"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 137, 139, 132, 156, 105, 17, 87)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 255, 51, 83, 51, 207, 102, 168)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 17, 141, 46, 239, 35, 224, 220)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_linter_deprecated_arg;
static const lean_ctor_object l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry_default = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedDeprecatedArgEntry = (const lean_object*)&l_Lean_Elab_instInhabitedDeprecatedArgEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deprecatedArgExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 157, 100, 72, 87, 251, 253, 102)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedArgExt;
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__0 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__1;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parameter `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__2 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__3;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__4 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__5;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` has been deprecated"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__6 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__7;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` has been deprecated, use `"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__8 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__9;
static const lean_string_object l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` instead"};
static const lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__10 = (const lean_object*)&l_Lean_Elab_formatDeprecatedArgMsg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_formatDeprecatedArgMsg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 138, .m_capacity = 138, .m_length = 137, .m_data = "`[deprecated_arg]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is still a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`; rename it to `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` is not a parameter of `"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`; remove it before adding `@[deprecated_arg]`"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Invalid `[deprecated_arg]` attribute syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DeprecatedArg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 168, 92, 104, 219, 200, 6, 160)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 45, 177, 228, 29, 219, 125, 116)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 25, 22, 75, 158, 128, 229, 101)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(107, 124, 96, 157, 76, 98, 131, 88)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 213, 49, 250, 165, 149, 52, 239)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 47, 237, 141, 165, 175, 79, 67)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 84, 26, 57, 180, 177, 26, 182)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(140, 241, 34, 119, 16, 121, 80, 72)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 144, 188, 92, 44, 216, 0, 99)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "deprecated_arg"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 7, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(45, 182, 86, 230, 168, 246, 164, 173)}};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mark a parameter as deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(lean_object* v_s_67_, lean_object* v_e_68_){
_start:
{
lean_object* v_declName_69_; lean_object* v_oldArg_70_; lean_object* v___y_72_; lean_object* v___x_75_; 
v_declName_69_ = lean_ctor_get(v_e_68_, 0);
lean_inc(v_declName_69_);
v_oldArg_70_ = lean_ctor_get(v_e_68_, 1);
lean_inc(v_oldArg_70_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_s_67_, v_declName_69_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
v___y_72_ = v___x_76_;
goto v___jp_71_;
}
else
{
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_75_, 1);
v___y_72_ = v_val_77_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v_inner_73_; lean_object* v___x_74_; 
v_inner_73_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_oldArg_70_, v_e_68_, v___y_72_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_69_, v_inner_73_, v_s_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(lean_object* v_es_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_array_mk(v_es_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_85_);
v___x_86_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_addDeprecatedArgEntry(v_b_83_, v___x_85_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_81_, v___x_87_);
v_i_81_ = v___x_88_;
v_b_83_ = v___x_86_;
goto _start;
}
else
{
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
lean_object* v___y_102_; uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_107_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_get_size(v___x_107_);
v___x_110_ = lean_nat_dec_lt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
v___y_102_ = v_b_100_;
goto v___jp_101_;
}
else
{
size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((size_t)0ULL);
v___x_112_ = lean_usize_of_nat(v___x_109_);
v___x_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__0(v___x_107_, v___x_111_, v___x_112_, v_b_100_);
v___y_102_ = v___x_113_;
goto v___jp_101_;
}
}
else
{
return v_b_100_;
}
v___jp_101_:
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_98_, v___x_103_);
v_i_98_ = v___x_104_;
v_b_100_ = v___y_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_114_, v_i_boxed_118_, v_stop_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(lean_object* v_initState_121_, lean_object* v_as_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_get_size(v_as_122_);
v___x_125_ = lean_nat_dec_lt(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v_initState_121_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_124_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0_spec__1(v_as_122_, v___x_126_, v___x_127_, v_initState_121_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_129_, lean_object* v_as_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2__spec__0(v_initState_129_, v_as_130_);
lean_dec_ref(v_as_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_));
v___x_151_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2____boxed(lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f(lean_object* v_env_154_, lean_object* v_declName_155_, lean_object* v_argName_156_){
_start:
{
lean_object* v___x_157_; lean_object* v_toEnvExtension_158_; lean_object* v_asyncMode_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_158_ = lean_ctor_get(v___x_157_, 0);
v_asyncMode_159_ = lean_ctor_get(v_toEnvExtension_158_, 2);
v___x_160_ = lean_box(1);
v___x_161_ = lean_box(0);
v___x_162_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_160_, v___x_157_, v_env_154_, v_asyncMode_159_, v___x_161_);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_162_, v_declName_155_);
lean_dec(v___x_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___x_166_; 
v_val_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_163_, 1);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_165_, v_argName_156_);
lean_dec(v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_findDeprecatedArg_x3f___boxed(lean_object* v_env_167_, lean_object* v_declName_168_, lean_object* v_argName_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_findDeprecatedArg_x3f(v_env_167_, v_declName_168_, v_argName_169_);
lean_dec(v_argName_169_);
lean_dec(v_declName_168_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__0));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__2));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__4));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__6));
v___x_182_ = l_Lean_stringToMessageData(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__8));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Elab_formatDeprecatedArgMsg___closed__10));
v___x_188_ = l_Lean_stringToMessageData(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_formatDeprecatedArgMsg(lean_object* v_entry_189_){
_start:
{
lean_object* v_declName_190_; lean_object* v_oldArg_191_; lean_object* v_newArg_x3f_192_; lean_object* v_text_x3f_193_; lean_object* v___y_195_; 
v_declName_190_ = lean_ctor_get(v_entry_189_, 0);
lean_inc(v_declName_190_);
v_oldArg_191_ = lean_ctor_get(v_entry_189_, 1);
lean_inc(v_oldArg_191_);
v_newArg_x3f_192_ = lean_ctor_get(v_entry_189_, 2);
lean_inc(v_newArg_x3f_192_);
v_text_x3f_193_ = lean_ctor_get(v_entry_189_, 3);
lean_inc(v_text_x3f_193_);
lean_dec_ref(v_entry_189_);
if (lean_obj_tag(v_newArg_x3f_192_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_202_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = 0;
v___x_207_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_206_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__7, &l_Lean_Elab_formatDeprecatedArgMsg___closed__7_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__7);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___y_195_ = v___x_210_;
goto v___jp_194_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_val_211_ = lean_ctor_get(v_newArg_x3f_192_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v_newArg_x3f_192_, 1);
v___x_212_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__3, &l_Lean_Elab_formatDeprecatedArgMsg___closed__3_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__3);
v___x_213_ = l_Lean_MessageData_ofName(v_oldArg_191_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__5, &l_Lean_Elab_formatDeprecatedArgMsg___closed__5_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__5);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = 0;
v___x_218_ = l_Lean_MessageData_ofConstName(v_declName_190_, v___x_217_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_216_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__9, &l_Lean_Elab_formatDeprecatedArgMsg___closed__9_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__9);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofName(v_val_211_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__11, &l_Lean_Elab_formatDeprecatedArgMsg___closed__11_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__11);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___y_195_ = v___x_225_;
goto v___jp_194_;
}
v___jp_194_:
{
if (lean_obj_tag(v_text_x3f_193_) == 0)
{
return v___y_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_val_196_ = lean_ctor_get(v_text_x3f_193_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_text_x3f_193_, 1);
v___x_197_ = lean_obj_once(&l_Lean_Elab_formatDeprecatedArgMsg___closed__1, &l_Lean_Elab_formatDeprecatedArgMsg___closed__1_once, _init_l_Lean_Elab_formatDeprecatedArgMsg___closed__1);
v___x_198_ = l_Lean_stringToMessageData(v_val_196_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0(lean_object* v_k_226_, lean_object* v_b_227_, lean_object* v_c_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
v___x_234_ = lean_apply_7(v_k_226_, v_b_227_, v_c_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0___boxed(lean_object* v_k_235_, lean_object* v_b_236_, lean_object* v_c_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0(v_k_235_, v_b_236_, v_c_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(lean_object* v_type_244_, lean_object* v_k_245_, uint8_t v_cleanupAnnotations_246_, uint8_t v_whnfType_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_253_, 0, v_k_245_);
v___x_254_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_244_, v___f_253_, v_cleanupAnnotations_246_, v_whnfType_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_254_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_type_271_, lean_object* v_k_272_, lean_object* v_cleanupAnnotations_273_, lean_object* v_whnfType_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_280_; uint8_t v_whnfType_boxed_281_; lean_object* v_res_282_; 
v_cleanupAnnotations_boxed_280_ = lean_unbox(v_cleanupAnnotations_273_);
v_whnfType_boxed_281_ = lean_unbox(v_whnfType_274_);
v_res_282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(v_type_271_, v_k_272_, v_cleanupAnnotations_boxed_280_, v_whnfType_boxed_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_283_, lean_object* v_type_284_, lean_object* v_k_285_, uint8_t v_cleanupAnnotations_286_, uint8_t v_whnfType_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(v_type_284_, v_k_285_, v_cleanupAnnotations_286_, v_whnfType_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_294_, lean_object* v_type_295_, lean_object* v_k_296_, lean_object* v_cleanupAnnotations_297_, lean_object* v_whnfType_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_304_; uint8_t v_whnfType_boxed_305_; lean_object* v_res_306_; 
v_cleanupAnnotations_boxed_304_ = lean_unbox(v_cleanupAnnotations_297_);
v_whnfType_boxed_305_ = lean_unbox(v_whnfType_298_);
v_res_306_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4(v_00_u03b1_294_, v_type_295_, v_k_296_, v_cleanupAnnotations_boxed_304_, v_whnfType_boxed_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(size_t v_sz_307_, size_t v_i_308_, lean_object* v_bs_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_bs_309_);
return v___x_315_;
}
else
{
lean_object* v_v_316_; lean_object* v___x_317_; lean_object* v_bs_x27_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_v_316_ = lean_array_uget(v_bs_309_, v_i_308_);
v___x_317_ = lean_unsigned_to_nat(0u);
v_bs_x27_318_ = lean_array_uset(v_bs_309_, v_i_308_, v___x_317_);
v___x_319_ = l_Lean_Expr_fvarId_x21(v_v_316_);
lean_dec(v_v_316_);
v___x_320_ = l_Lean_FVarId_getDecl___redArg(v___x_319_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = l_Lean_LocalDecl_userName(v_a_321_);
lean_dec(v_a_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_308_, v___x_323_);
v___x_325_ = lean_array_uset(v_bs_x27_318_, v_i_308_, v___x_322_);
v_i_308_ = v___x_324_;
v_bs_309_ = v___x_325_;
goto _start;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_bs_x27_318_);
v_a_327_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_320_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_320_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_bs_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_343_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_boxed_342_, v_i_boxed_343_, v_bs_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v_xs_345_, lean_object* v_x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_352_; size_t v___x_353_; lean_object* v___x_354_; 
v_sz_352_ = lean_array_size(v_xs_345_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_352_, v___x_353_, v_xs_345_, v___y_347_, v___y_349_, v___y_350_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v_xs_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v_xs_355_, v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_x_356_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v_addEntryFn_363_, lean_object* v___x_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_importedEntries_366_; lean_object* v_state_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_importedEntries_366_ = lean_ctor_get(v_s_365_, 0);
v_state_367_ = lean_ctor_get(v_s_365_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_s_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v_s_365_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_state_367_);
lean_inc(v_importedEntries_366_);
lean_dec(v_s_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_state_371_; lean_object* v___x_373_; 
v_state_371_ = lean_apply_2(v_addEntryFn_363_, v_state_367_, v___x_364_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_state_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_importedEntries_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_state_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(lean_object* v_oldArg_376_, lean_object* v_as_377_, size_t v_i_378_, size_t v_stop_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_eq(v_i_378_, v_stop_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_uget_borrowed(v_as_377_, v_i_378_);
v___x_382_ = lean_name_eq(v___x_381_, v_oldArg_376_);
if (v___x_382_ == 0)
{
size_t v___x_383_; size_t v___x_384_; 
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_add(v_i_378_, v___x_383_);
v_i_378_ = v___x_384_;
goto _start;
}
else
{
return v___x_382_;
}
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5___boxed(lean_object* v_oldArg_387_, lean_object* v_as_388_, lean_object* v_i_389_, lean_object* v_stop_390_){
_start:
{
size_t v_i_boxed_391_; size_t v_stop_boxed_392_; uint8_t v_res_393_; lean_object* v_r_394_; 
v_i_boxed_391_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_stop_boxed_392_ = lean_unbox_usize(v_stop_390_);
lean_dec(v_stop_390_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(v_oldArg_387_, v_as_388_, v_i_boxed_391_, v_stop_boxed_392_);
lean_dec_ref(v_as_388_);
lean_dec(v_oldArg_387_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
lean_ctor_set(v___x_401_, 3, v___x_400_);
lean_ctor_set(v___x_401_, 4, v___x_399_);
lean_ctor_set(v___x_401_, 5, v___x_399_);
lean_ctor_set(v___x_401_, 6, v___x_399_);
lean_ctor_set(v___x_401_, 7, v___x_399_);
lean_ctor_set(v___x_401_, 8, v___x_399_);
lean_ctor_set(v___x_401_, 9, v___x_399_);
lean_ctor_set(v___x_401_, 10, v___x_399_);
lean_ctor_set(v___x_401_, 11, v___x_398_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(32u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((size_t)5ULL);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_unsigned_to_nat(32u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_410_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_406_);
lean_ctor_set(v___x_410_, 3, v___x_406_);
lean_ctor_set_usize(v___x_410_, 4, v___x_405_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_box(1);
v___x_412_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__4);
v___x_413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__1);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; lean_object* v_toCold_420_; lean_object* v_env_421_; lean_object* v_options_422_; uint8_t v___x_423_; lean_object* v_env_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_419_ = lean_st_ref_get(v___y_417_);
v_toCold_420_ = lean_ctor_get(v___y_416_, 0);
v_env_421_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_421_);
lean_dec(v___x_419_);
v_options_422_ = lean_ctor_get(v_toCold_420_, 2);
v___x_423_ = 0;
v_env_424_ = l_Lean_Environment_setRecordingDeps(v_env_421_, v___x_423_);
v___x_425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5);
lean_inc_ref(v_options_422_);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v_env_424_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set(v___x_427_, 3, v_options_422_);
v___x_428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_msgData_415_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_msgData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v_msgData_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 2);
v___x_440_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v_msg_435_, v___y_436_, v___y_437_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_inc(v_ref_439_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_ref_439_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(lean_object* v_ref_455_, lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_toCold_460_; lean_object* v_currRecDepth_461_; lean_object* v_ref_462_; uint16_t v_optionFlags_463_; uint8_t v_suppressElabErrors_464_; uint8_t v_checkDeprecated_465_; uint8_t v_isRecordingDeps_466_; lean_object* v_ref_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_toCold_460_ = lean_ctor_get(v___y_457_, 0);
v_currRecDepth_461_ = lean_ctor_get(v___y_457_, 1);
v_ref_462_ = lean_ctor_get(v___y_457_, 2);
v_optionFlags_463_ = lean_ctor_get_uint16(v___y_457_, sizeof(void*)*3);
v_suppressElabErrors_464_ = lean_ctor_get_uint8(v___y_457_, sizeof(void*)*3 + 2);
v_checkDeprecated_465_ = lean_ctor_get_uint8(v___y_457_, sizeof(void*)*3 + 3);
v_isRecordingDeps_466_ = lean_ctor_get_uint8(v___y_457_, sizeof(void*)*3 + 4);
v_ref_467_ = l_Lean_replaceRef(v_ref_455_, v_ref_462_);
lean_inc(v_currRecDepth_461_);
lean_inc_ref(v_toCold_460_);
v___x_468_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_468_, 0, v_toCold_460_);
lean_ctor_set(v___x_468_, 1, v_currRecDepth_461_);
lean_ctor_set(v___x_468_, 2, v_ref_467_);
lean_ctor_set_uint16(v___x_468_, sizeof(void*)*3, v_optionFlags_463_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*3 + 2, v_suppressElabErrors_464_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*3 + 3, v_checkDeprecated_465_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*3 + 4, v_isRecordingDeps_466_);
v___x_469_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_456_, v___x_468_, v___y_458_);
lean_dec_ref_known(v___x_468_, 3);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_ref_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_470_, v_msg_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v_ref_470_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__0));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__2));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_497_, lean_object* v_declHint_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_env_503_; uint8_t v___x_504_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_st_ref_get(v___y_499_);
v_env_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc_ref(v_env_503_);
lean_dec(v___x_502_);
v___x_504_ = l_Lean_Name_isAnonymous(v_declHint_498_);
if (v___x_504_ == 0)
{
uint8_t v_isExporting_505_; 
v_isExporting_505_ = lean_ctor_get_uint8(v_env_503_, sizeof(void*)*13);
if (v_isExporting_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_env_503_);
lean_dec(v_declHint_498_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v_msg_497_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
lean_inc_ref(v_env_503_);
v___x_507_ = l_Lean_Environment_setExporting(v_env_503_, v___x_504_);
lean_inc(v_declHint_498_);
lean_inc_ref(v___x_507_);
v___x_508_ = l_Lean_Environment_contains(v___x_507_, v_declHint_498_, v_isExporting_505_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v___x_507_);
lean_dec_ref(v_env_503_);
lean_dec(v_declHint_498_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_msg_497_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_c_515_; lean_object* v___x_516_; 
v___x_510_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__2);
v___x_511_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__5);
v___x_512_ = l_Lean_Options_empty;
lean_inc_ref(v___x_507_);
v___x_513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_513_, 0, v___x_507_);
lean_ctor_set(v___x_513_, 1, v___x_510_);
lean_ctor_set(v___x_513_, 2, v___x_511_);
lean_ctor_set(v___x_513_, 3, v___x_512_);
lean_inc(v_declHint_498_);
v___x_514_ = l_Lean_MessageData_ofConstName(v_declHint_498_, v___x_504_);
v_c_515_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_515_, 0, v___x_513_);
lean_ctor_set(v_c_515_, 1, v___x_514_);
v___x_516_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_507_, v_declHint_498_);
lean_dec_ref(v___x_507_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_env_503_);
lean_dec(v_declHint_498_);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_c_515_);
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_MessageData_note(v___x_520_);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v_msg_497_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_558_; 
v_val_524_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_558_ == 0)
{
v___x_526_ = v___x_516_;
v_isShared_527_ = v_isSharedCheck_558_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_516_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_558_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_moduleNames_529_; lean_object* v_mod_530_; uint8_t v___x_531_; 
v___x_528_ = l_Lean_Environment_header(v_env_503_);
lean_dec_ref(v_env_503_);
v_moduleNames_529_ = lean_ctor_get(v___x_528_, 4);
lean_inc_ref(v_moduleNames_529_);
lean_dec_ref(v___x_528_);
v_mod_530_ = lean_array_get(v___x_501_, v_moduleNames_529_, v_val_524_);
lean_dec(v_val_524_);
lean_dec_ref(v_moduleNames_529_);
v___x_531_ = l_Lean_isPrivateName(v_declHint_498_);
lean_dec(v_declHint_498_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_c_515_);
v___x_534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_MessageData_ofName(v_mod_530_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_MessageData_note(v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v_msg_497_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
lean_ctor_set(v___x_526_, 0, v___x_541_);
v___x_543_ = v___x_526_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_c_515_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_ofName(v_mod_530_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_MessageData_note(v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v_msg_497_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
lean_ctor_set(v___x_526_, 0, v___x_554_);
v___x_556_ = v___x_526_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v_env_503_);
lean_dec(v_declHint_498_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_msg_497_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_560_, lean_object* v_declHint_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_560_, v_declHint_561_, v___y_562_);
lean_dec(v___y_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(lean_object* v_msg_565_, lean_object* v_declHint_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v___x_570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_565_, v_declHint_566_, v___y_568_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_575_ = l_Lean_unknownIdentifierMessageTag;
v___x_576_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_576_);
v___x_578_ = v___x_573_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12___boxed(lean_object* v_msg_581_, lean_object* v_declHint_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_581_, v_declHint_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_ref_587_, lean_object* v_msg_588_, lean_object* v_declHint_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12(v_msg_588_, v_declHint_589_, v___y_590_, v___y_591_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref(v___x_593_);
v___x_595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_587_, v_a_594_, v___y_590_, v___y_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_ref_596_, lean_object* v_msg_597_, lean_object* v_declHint_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_596_, v_msg_597_, v_declHint_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_ref_596_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__0));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__2));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(lean_object* v_ref_609_, lean_object* v_constName_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_614_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__1);
v___x_615_ = 0;
lean_inc(v_constName_610_);
v___x_616_ = l_Lean_MessageData_ofConstName(v_constName_610_, v___x_615_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_614_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_609_, v___x_619_, v_constName_610_, v___y_611_, v___y_612_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_ref_621_, lean_object* v_constName_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_621_, v_constName_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v_ref_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(lean_object* v_constName_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_ref_631_; lean_object* v___x_632_; 
v_ref_631_ = lean_ctor_get(v___y_628_, 2);
v___x_632_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_631_, v_constName_627_, v___y_628_, v___y_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(lean_object* v_constName_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(lean_object* v_constName_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; lean_object* v_env_643_; uint8_t v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_st_ref_get(v___y_640_);
v_env_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_env_643_);
lean_dec(v___x_642_);
v___x_644_ = 0;
lean_inc(v_constName_638_);
v___x_645_ = l_Lean_Environment_find_x3f(v_env_643_, v_constName_638_, v___x_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_638_, v___y_639_, v___y_640_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_constName_638_);
v_val_647_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_val_647_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 0);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_val_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3___boxed(lean_object* v_constName_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(v_constName_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 1)
{
lean_object* v_pre_669_; 
v_pre_669_ = lean_ctor_get(v_x_668_, 0);
switch(lean_obj_tag(v_pre_669_))
{
case 1:
{
lean_object* v_pre_670_; 
v_pre_670_ = lean_ctor_get(v_pre_669_, 0);
switch(lean_obj_tag(v_pre_670_))
{
case 0:
{
lean_object* v_str_671_; lean_object* v_str_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_str_671_ = lean_ctor_get(v_x_668_, 1);
v_str_672_ = lean_ctor_get(v_pre_669_, 1);
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_));
v___x_674_ = lean_string_dec_eq(v_str_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__0));
v___x_676_ = lean_string_dec_eq(v_str_672_, v___x_675_);
if (v___x_676_ == 0)
{
return v___x_676_;
}
else
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__1));
v___x_678_ = lean_string_dec_eq(v_str_671_, v___x_677_);
if (v___x_678_ == 0)
{
return v___x_678_;
}
else
{
return v_suppressElabErrors_667_;
}
}
}
else
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__2));
v___x_680_ = lean_string_dec_eq(v_str_671_, v___x_679_);
if (v___x_680_ == 0)
{
return v___x_680_;
}
else
{
return v_suppressElabErrors_667_;
}
}
}
case 1:
{
lean_object* v_pre_681_; 
v_pre_681_ = lean_ctor_get(v_pre_670_, 0);
if (lean_obj_tag(v_pre_681_) == 0)
{
lean_object* v_str_682_; lean_object* v_str_683_; lean_object* v_str_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_str_682_ = lean_ctor_get(v_x_668_, 1);
v_str_683_ = lean_ctor_get(v_pre_669_, 1);
v_str_684_ = lean_ctor_get(v_pre_670_, 1);
v___x_685_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__3));
v___x_686_ = lean_string_dec_eq(v_str_684_, v___x_685_);
if (v___x_686_ == 0)
{
return v___x_686_;
}
else
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__4));
v___x_688_ = lean_string_dec_eq(v_str_683_, v___x_687_);
if (v___x_688_ == 0)
{
return v___x_688_;
}
else
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__5));
v___x_690_ = lean_string_dec_eq(v_str_682_, v___x_689_);
if (v___x_690_ == 0)
{
return v___x_690_;
}
else
{
return v_suppressElabErrors_667_;
}
}
}
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
default: 
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
}
}
case 0:
{
lean_object* v_str_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_str_693_ = lean_ctor_get(v_x_668_, 1);
v___x_694_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___closed__6));
v___x_695_ = lean_string_dec_eq(v_str_693_, v___x_694_);
if (v___x_695_ == 0)
{
return v___x_695_;
}
else
{
return v_suppressElabErrors_667_;
}
}
default: 
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_698_, lean_object* v_x_699_){
_start:
{
uint8_t v_suppressElabErrors_boxed_700_; uint8_t v_res_701_; lean_object* v_r_702_; 
v_suppressElabErrors_boxed_700_ = lean_unbox(v_suppressElabErrors_698_);
v_res_701_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_700_, v_x_699_);
lean_dec(v_x_699_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(lean_object* v_opts_703_, lean_object* v_opt_704_){
_start:
{
lean_object* v_name_705_; lean_object* v_defValue_706_; lean_object* v_map_707_; lean_object* v___x_708_; 
v_name_705_ = lean_ctor_get(v_opt_704_, 0);
v_defValue_706_ = lean_ctor_get(v_opt_704_, 1);
v_map_707_ = lean_ctor_get(v_opts_703_, 0);
v___x_708_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_707_, v_name_705_);
if (lean_obj_tag(v___x_708_) == 0)
{
uint8_t v___x_709_; 
v___x_709_ = lean_unbox(v_defValue_706_);
return v___x_709_;
}
else
{
lean_object* v_val_710_; 
v_val_710_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v___x_708_, 1);
if (lean_obj_tag(v_val_710_) == 1)
{
uint8_t v_v_711_; 
v_v_711_ = lean_ctor_get_uint8(v_val_710_, 0);
lean_dec_ref_known(v_val_710_, 0);
return v_v_711_;
}
else
{
uint8_t v___x_712_; 
lean_dec(v_val_710_);
v___x_712_ = lean_unbox(v_defValue_706_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_opts_713_, lean_object* v_opt_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(v_opts_713_, v_opt_714_);
lean_dec_ref(v_opt_714_);
lean_dec_ref(v_opts_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(lean_object* v_ref_718_, lean_object* v_msgData_719_, uint8_t v_severity_720_, uint8_t v_isSilent_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; lean_object* v___y_732_; lean_object* v_toCold_733_; lean_object* v___y_734_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_766_; uint8_t v___y_767_; uint8_t v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_793_; uint8_t v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; uint8_t v___y_800_; uint8_t v___y_801_; uint8_t v___x_811_; uint8_t v___y_813_; uint8_t v___x_819_; 
v___x_811_ = 2;
v___x_819_ = l_Lean_instBEqMessageSeverity_beq(v_severity_720_, v___x_811_);
if (v___x_819_ == 0)
{
v___y_813_ = v___x_819_;
goto v___jp_812_;
}
else
{
uint8_t v___x_820_; 
lean_inc_ref(v_msgData_719_);
v___x_820_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_719_);
if (v___x_820_ == 0)
{
v___y_813_ = v___x_820_;
goto v___jp_812_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v_msgData_719_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
v___jp_725_:
{
lean_object* v_currNamespace_735_; lean_object* v_openDecls_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_env_741_; lean_object* v_nextMacroScope_742_; lean_object* v_ngen_743_; lean_object* v_auxDeclNGen_744_; lean_object* v_traceState_745_; lean_object* v_cache_746_; lean_object* v_recordedDeps_747_; lean_object* v_messages_748_; lean_object* v_infoState_749_; lean_object* v_snapshotTasks_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_761_; 
v_currNamespace_735_ = lean_ctor_get(v_toCold_733_, 4);
v_openDecls_736_ = lean_ctor_get(v_toCold_733_, 5);
lean_inc(v_openDecls_736_);
lean_inc(v_currNamespace_735_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_currNamespace_735_);
lean_ctor_set(v___x_737_, 1, v_openDecls_736_);
v___x_738_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___y_732_);
lean_inc_ref(v___y_728_);
lean_inc_ref(v___y_730_);
v___x_739_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_739_, 0, v___y_730_);
lean_ctor_set(v___x_739_, 1, v___y_727_);
lean_ctor_set(v___x_739_, 2, v___y_726_);
lean_ctor_set(v___x_739_, 3, v___y_728_);
lean_ctor_set(v___x_739_, 4, v___x_738_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*5, v___y_731_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*5 + 1, v___y_729_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*5 + 2, v_isSilent_721_);
v___x_740_ = lean_st_ref_take(v___y_734_);
v_env_741_ = lean_ctor_get(v___x_740_, 0);
v_nextMacroScope_742_ = lean_ctor_get(v___x_740_, 1);
v_ngen_743_ = lean_ctor_get(v___x_740_, 2);
v_auxDeclNGen_744_ = lean_ctor_get(v___x_740_, 3);
v_traceState_745_ = lean_ctor_get(v___x_740_, 4);
v_cache_746_ = lean_ctor_get(v___x_740_, 5);
v_recordedDeps_747_ = lean_ctor_get(v___x_740_, 6);
v_messages_748_ = lean_ctor_get(v___x_740_, 7);
v_infoState_749_ = lean_ctor_get(v___x_740_, 8);
v_snapshotTasks_750_ = lean_ctor_get(v___x_740_, 9);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_761_ == 0)
{
v___x_752_ = v___x_740_;
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snapshotTasks_750_);
lean_inc(v_infoState_749_);
lean_inc(v_messages_748_);
lean_inc(v_recordedDeps_747_);
lean_inc(v_cache_746_);
lean_inc(v_traceState_745_);
lean_inc(v_auxDeclNGen_744_);
lean_inc(v_ngen_743_);
lean_inc(v_nextMacroScope_742_);
lean_inc(v_env_741_);
lean_dec(v___x_740_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = lean_box(0);
v___x_755_ = l_Lean_MessageLog_add(v___x_739_, v_messages_748_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 7, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_env_741_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_nextMacroScope_742_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_ngen_743_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_auxDeclNGen_744_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_traceState_745_);
lean_ctor_set(v_reuseFailAlloc_760_, 5, v_cache_746_);
lean_ctor_set(v_reuseFailAlloc_760_, 6, v_recordedDeps_747_);
lean_ctor_set(v_reuseFailAlloc_760_, 7, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_760_, 8, v_infoState_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 9, v_snapshotTasks_750_);
v___x_757_ = v_reuseFailAlloc_760_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_st_ref_put(v___y_734_, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_754_);
return v___x_759_;
}
}
}
v___jp_762_:
{
lean_object* v_fileName_771_; lean_object* v_fileMap_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_788_; 
v_fileName_771_ = lean_ctor_get(v___y_765_, 0);
v_fileMap_772_ = lean_ctor_get(v___y_765_, 1);
v___x_773_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_719_);
v___x_774_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1(v___x_773_, v___y_722_, v___y_723_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref_n(v_fileMap_772_, 2);
v___x_779_ = l_Lean_FileMap_toPosition(v_fileMap_772_, v___y_769_);
lean_dec(v___y_769_);
v___x_780_ = l_Lean_FileMap_toPosition(v_fileMap_772_, v___y_770_);
lean_dec(v___y_770_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___closed__0));
if (v___y_767_ == 0)
{
lean_del_object(v___x_777_);
lean_dec_ref(v___y_764_);
v___y_726_ = v___x_781_;
v___y_727_ = v___x_779_;
v___y_728_ = v___x_782_;
v___y_729_ = v___y_766_;
v___y_730_ = v_fileName_771_;
v___y_731_ = v___y_768_;
v___y_732_ = v_a_775_;
v_toCold_733_ = v___y_763_;
v___y_734_ = v___y_723_;
goto v___jp_725_;
}
else
{
uint8_t v___x_783_; 
lean_inc(v_a_775_);
v___x_783_ = l_Lean_MessageData_hasTag(v___y_764_, v_a_775_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_781_, 1);
lean_dec_ref(v___x_779_);
lean_dec(v_a_775_);
v___x_784_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_784_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_del_object(v___x_777_);
v___y_726_ = v___x_781_;
v___y_727_ = v___x_779_;
v___y_728_ = v___x_782_;
v___y_729_ = v___y_766_;
v___y_730_ = v_fileName_771_;
v___y_731_ = v___y_768_;
v___y_732_ = v_a_775_;
v_toCold_733_ = v___y_763_;
v___y_734_ = v___y_723_;
goto v___jp_725_;
}
}
}
}
v___jp_789_:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Syntax_getTailPos_x3f(v___y_793_, v___y_795_);
lean_dec(v___y_793_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_inc(v___y_796_);
v___y_763_ = v___y_790_;
v___y_764_ = v___y_791_;
v___y_765_ = v___y_790_;
v___y_766_ = v___y_794_;
v___y_767_ = v___y_792_;
v___y_768_ = v___y_795_;
v___y_769_ = v___y_796_;
v___y_770_ = v___y_796_;
goto v___jp_762_;
}
else
{
lean_object* v_val_798_; 
v_val_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v___x_797_, 1);
v___y_763_ = v___y_790_;
v___y_764_ = v___y_791_;
v___y_765_ = v___y_790_;
v___y_766_ = v___y_794_;
v___y_767_ = v___y_792_;
v___y_768_ = v___y_795_;
v___y_769_ = v___y_796_;
v___y_770_ = v_val_798_;
goto v___jp_762_;
}
}
v___jp_799_:
{
lean_object* v_toCold_802_; lean_object* v_ref_803_; uint8_t v_suppressElabErrors_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v_ref_807_; lean_object* v___x_808_; 
v_toCold_802_ = lean_ctor_get(v___y_722_, 0);
v_ref_803_ = lean_ctor_get(v___y_722_, 2);
v_suppressElabErrors_804_ = lean_ctor_get_uint8(v___y_722_, sizeof(void*)*3 + 2);
v___x_805_ = lean_box(v_suppressElabErrors_804_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_806_, 0, v___x_805_);
v_ref_807_ = l_Lean_replaceRef(v_ref_718_, v_ref_803_);
v___x_808_ = l_Lean_Syntax_getPos_x3f(v_ref_807_, v___y_800_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_unsigned_to_nat(0u);
v___y_790_ = v_toCold_802_;
v___y_791_ = v___f_806_;
v___y_792_ = v_suppressElabErrors_804_;
v___y_793_ = v_ref_807_;
v___y_794_ = v___y_801_;
v___y_795_ = v___y_800_;
v___y_796_ = v___x_809_;
goto v___jp_789_;
}
else
{
lean_object* v_val_810_; 
v_val_810_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_val_810_);
lean_dec_ref_known(v___x_808_, 1);
v___y_790_ = v_toCold_802_;
v___y_791_ = v___f_806_;
v___y_792_ = v_suppressElabErrors_804_;
v___y_793_ = v_ref_807_;
v___y_794_ = v___y_801_;
v___y_795_ = v___y_800_;
v___y_796_ = v_val_810_;
goto v___jp_789_;
}
}
v___jp_812_:
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = 1;
v___x_815_ = l_Lean_instBEqMessageSeverity_beq(v_severity_720_, v___x_814_);
if (v___x_815_ == 0)
{
v___y_800_ = v___y_813_;
v___y_801_ = v_severity_720_;
goto v___jp_799_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_816_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_722_);
v___x_817_ = l_Lean_warningAsError;
v___x_818_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5_spec__8(v___x_816_, v___x_817_);
lean_dec_ref(v___x_816_);
if (v___x_818_ == 0)
{
v___y_800_ = v___y_813_;
v___y_801_ = v_severity_720_;
goto v___jp_799_;
}
else
{
v___y_800_ = v___y_813_;
v___y_801_ = v___x_811_;
goto v___jp_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5___boxed(lean_object* v_ref_823_, lean_object* v_msgData_824_, lean_object* v_severity_825_, lean_object* v_isSilent_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v_severity_boxed_830_; uint8_t v_isSilent_boxed_831_; lean_object* v_res_832_; 
v_severity_boxed_830_ = lean_unbox(v_severity_825_);
v_isSilent_boxed_831_ = lean_unbox(v_isSilent_826_);
v_res_832_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_823_, v_msgData_824_, v_severity_boxed_830_, v_isSilent_boxed_831_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v_ref_823_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_msgData_833_, uint8_t v_severity_834_, uint8_t v_isSilent_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_ref_839_; lean_object* v___x_840_; 
v_ref_839_ = lean_ctor_get(v___y_836_, 2);
v___x_840_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3_spec__5(v_ref_839_, v_msgData_833_, v_severity_834_, v_isSilent_835_, v___y_836_, v___y_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_msgData_841_, lean_object* v_severity_842_, lean_object* v_isSilent_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v_severity_boxed_847_; uint8_t v_isSilent_boxed_848_; lean_object* v_res_849_; 
v_severity_boxed_847_ = lean_unbox(v_severity_842_);
v_isSilent_boxed_848_ = lean_unbox(v_isSilent_843_);
v_res_849_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(v_msgData_841_, v_severity_boxed_847_, v_isSilent_boxed_848_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(lean_object* v_msgData_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = 1;
v___x_855_ = 0;
v___x_856_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2_spec__3(v_msgData_850_, v___x_854_, v___x_855_, v___y_851_, v___y_852_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2___boxed(lean_object* v_msgData_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(v_msgData_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_861_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__4_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__6_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__8_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__10_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__0);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_884_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_ctor_set(v___x_884_, 3, v___x_883_);
lean_ctor_set(v___x_884_, 4, v___x_883_);
lean_ctor_set(v___x_884_, 5, v___x_883_);
lean_ctor_set(v___x_884_, 6, v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
lean_ctor_set(v___x_886_, 3, v___x_885_);
lean_ctor_set(v___x_886_, 4, v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__15_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v___f_898_, lean_object* v___x_899_, lean_object* v_declName_900_, lean_object* v_stx_901_, uint8_t v___kind_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v_nextMacroScope_909_; lean_object* v_ngen_910_; lean_object* v_auxDeclNGen_911_; lean_object* v_traceState_912_; lean_object* v_recordedDeps_913_; lean_object* v_messages_914_; lean_object* v_infoState_915_; lean_object* v_snapshotTasks_916_; lean_object* v___y_917_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; 
v___x_922_ = l_Lean_Name_mkStr2(v___x_893_, v___x_894_);
lean_inc(v_stx_901_);
v___x_923_ = l_Lean_Syntax_isOfKind(v_stx_901_, v___x_922_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec_ref(v___f_898_);
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___x_1128_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1129_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1128_, v___y_903_, v___y_904_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v_oldId_1131_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v_since_x3f_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v_text_x3f_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v_newId_x3f_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
v_oldId_1131_ = l_Lean_Syntax_getArg(v_stx_901_, v___x_1130_);
v___x_1178_ = l_Lean_Syntax_getArg(v_stx_901_, v___x_899_);
v___x_1179_ = l_Lean_Syntax_isNone(v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; 
lean_inc(v___x_1178_);
v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1130_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1178_);
lean_dec(v_oldId_1131_);
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec_ref(v___f_898_);
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1182_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1181_, v___y_903_, v___y_904_);
return v___x_1182_;
}
else
{
lean_object* v_newId_x3f_1183_; lean_object* v___x_1184_; 
v_newId_x3f_1183_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_896_);
lean_dec(v___x_1178_);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_newId_x3f_1183_);
v_newId_x3f_1166_ = v___x_1184_;
v___y_1167_ = v___y_903_;
v___y_1168_ = v___y_904_;
goto v___jp_1165_;
}
}
else
{
lean_object* v___x_1185_; 
lean_dec(v___x_1178_);
v___x_1185_ = lean_box(0);
v_newId_x3f_1166_ = v___x_1185_;
v___y_1167_ = v___y_903_;
v___y_1168_ = v___y_904_;
goto v___jp_1165_;
}
v___jp_1132_:
{
lean_object* v_oldArg_1138_; 
v_oldArg_1138_ = l_Lean_TSyntax_getId(v_oldId_1131_);
lean_dec(v_oldId_1131_);
if (lean_obj_tag(v___y_1133_) == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_box(0);
v___y_1109_ = v_oldArg_1138_;
v___y_1110_ = v_since_x3f_1135_;
v___y_1111_ = v___y_1136_;
v___y_1112_ = v___y_1137_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___x_1139_;
goto v___jp_1108_;
}
else
{
lean_object* v_val_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v_val_1140_ = lean_ctor_get(v___y_1133_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___y_1133_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1142_ = v___y_1133_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_val_1140_);
lean_dec(v___y_1133_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_TSyntax_getId(v_val_1140_);
lean_dec(v_val_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v___y_1109_ = v_oldArg_1138_;
v___y_1110_ = v_since_x3f_1135_;
v___y_1111_ = v___y_1136_;
v___y_1112_ = v___y_1137_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___x_1146_;
goto v___jp_1108_;
}
}
}
}
v___jp_1149_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(4u);
v___x_1156_ = l_Lean_Syntax_getArg(v_stx_901_, v___x_1155_);
v___x_1157_ = l_Lean_Syntax_isNone(v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1156_);
v___x_1159_ = l_Lean_Syntax_matchesNull(v___x_1156_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v___x_1156_);
lean_dec(v_text_x3f_1152_);
lean_dec(v___y_1150_);
lean_dec(v_oldId_1131_);
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec_ref(v___f_898_);
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1160_, v___y_1153_, v___y_1154_);
return v___x_1161_;
}
else
{
lean_object* v_since_x3f_1162_; lean_object* v___x_1163_; 
v_since_x3f_1162_ = l_Lean_Syntax_getArg(v___x_1156_, v___y_1151_);
lean_dec(v___x_1156_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_since_x3f_1162_);
v___y_1133_ = v___y_1150_;
v___y_1134_ = v_text_x3f_1152_;
v_since_x3f_1135_ = v___x_1163_;
v___y_1136_ = v___y_1153_;
v___y_1137_ = v___y_1154_;
goto v___jp_1132_;
}
}
else
{
lean_object* v___x_1164_; 
lean_dec(v___x_1156_);
v___x_1164_ = lean_box(0);
v___y_1133_ = v___y_1150_;
v___y_1134_ = v_text_x3f_1152_;
v_since_x3f_1135_ = v___x_1164_;
v___y_1136_ = v___y_1153_;
v___y_1137_ = v___y_1154_;
goto v___jp_1132_;
}
}
v___jp_1165_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = l_Lean_Syntax_getArg(v_stx_901_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_isNone(v___x_1170_);
if (v___x_1171_ == 0)
{
uint8_t v___x_1172_; 
lean_inc(v___x_1170_);
v___x_1172_ = l_Lean_Syntax_matchesNull(v___x_1170_, v___x_1130_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v___x_1170_);
lean_dec(v_newId_x3f_1166_);
lean_dec(v_oldId_1131_);
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec_ref(v___f_898_);
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___x_1173_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1174_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1173_, v___y_1167_, v___y_1168_);
return v___x_1174_;
}
else
{
lean_object* v_text_x3f_1175_; lean_object* v___x_1176_; 
v_text_x3f_1175_ = l_Lean_Syntax_getArg(v___x_1170_, v___x_896_);
lean_dec(v___x_1170_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_text_x3f_1175_);
v___y_1150_ = v_newId_x3f_1166_;
v___y_1151_ = v___x_1169_;
v_text_x3f_1152_ = v___x_1176_;
v___y_1153_ = v___y_1167_;
v___y_1154_ = v___y_1168_;
goto v___jp_1149_;
}
}
else
{
lean_object* v___x_1177_; 
lean_dec(v___x_1170_);
v___x_1177_ = lean_box(0);
v___y_1150_ = v_newId_x3f_1166_;
v___y_1151_ = v___x_1169_;
v_text_x3f_1152_ = v___x_1177_;
v___y_1153_ = v___y_1167_;
v___y_1154_ = v___y_1168_;
goto v___jp_1149_;
}
}
}
v___jp_906_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_919_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_919_, 0, v___y_917_);
lean_ctor_set(v___x_919_, 1, v_nextMacroScope_909_);
lean_ctor_set(v___x_919_, 2, v_ngen_910_);
lean_ctor_set(v___x_919_, 3, v_auxDeclNGen_911_);
lean_ctor_set(v___x_919_, 4, v_traceState_912_);
lean_ctor_set(v___x_919_, 5, v___x_918_);
lean_ctor_set(v___x_919_, 6, v_recordedDeps_913_);
lean_ctor_set(v___x_919_, 7, v_messages_914_);
lean_ctor_set(v___x_919_, 8, v_infoState_915_);
lean_ctor_set(v___x_919_, 9, v_snapshotTasks_916_);
v___x_920_ = lean_st_ref_put(v___y_908_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___y_907_);
return v___x_921_;
}
v___jp_924_:
{
lean_object* v___x_930_; lean_object* v_env_931_; lean_object* v_nextMacroScope_932_; lean_object* v_ngen_933_; lean_object* v_auxDeclNGen_934_; lean_object* v_traceState_935_; lean_object* v_recordedDeps_936_; lean_object* v_messages_937_; lean_object* v_infoState_938_; lean_object* v_snapshotTasks_939_; lean_object* v___x_940_; lean_object* v_toEnvExtension_941_; lean_object* v_addEntryFn_942_; lean_object* v_asyncMode_943_; uint8_t v_logWrites_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___f_947_; 
v___x_930_ = lean_st_ref_take(v___y_929_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_env_931_);
v_nextMacroScope_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_nextMacroScope_932_);
v_ngen_933_ = lean_ctor_get(v___x_930_, 2);
lean_inc_ref(v_ngen_933_);
v_auxDeclNGen_934_ = lean_ctor_get(v___x_930_, 3);
lean_inc_ref(v_auxDeclNGen_934_);
v_traceState_935_ = lean_ctor_get(v___x_930_, 4);
lean_inc_ref(v_traceState_935_);
v_recordedDeps_936_ = lean_ctor_get(v___x_930_, 6);
lean_inc_ref(v_recordedDeps_936_);
v_messages_937_ = lean_ctor_get(v___x_930_, 7);
lean_inc_ref(v_messages_937_);
v_infoState_938_ = lean_ctor_get(v___x_930_, 8);
lean_inc_ref(v_infoState_938_);
v_snapshotTasks_939_ = lean_ctor_get(v___x_930_, 9);
lean_inc_ref(v_snapshotTasks_939_);
lean_dec(v___x_930_);
v___x_940_ = l_Lean_Elab_deprecatedArgExt;
v_toEnvExtension_941_ = lean_ctor_get(v___x_940_, 0);
v_addEntryFn_942_ = lean_ctor_get(v___x_940_, 3);
v_asyncMode_943_ = lean_ctor_get(v_toEnvExtension_941_, 2);
v_logWrites_944_ = lean_ctor_get_uint8(v_toEnvExtension_941_, sizeof(void*)*6);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_946_, 0, v_declName_900_);
lean_ctor_set(v___x_946_, 1, v___y_925_);
lean_ctor_set(v___x_946_, 2, v___y_927_);
lean_ctor_set(v___x_946_, 3, v___y_926_);
lean_ctor_set(v___x_946_, 4, v___y_928_);
lean_inc(v_addEntryFn_942_);
v___f_947_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_947_, 0, v_addEntryFn_942_);
lean_closure_set(v___f_947_, 1, v___x_946_);
if (v_logWrites_944_ == 0)
{
lean_object* v___x_948_; 
lean_inc_ref(v_toEnvExtension_941_);
v___x_948_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_941_, v_env_931_, v___f_947_, v_asyncMode_943_, v___x_895_, v___x_923_);
v___y_907_ = v___x_945_;
v___y_908_ = v___y_929_;
v_nextMacroScope_909_ = v_nextMacroScope_932_;
v_ngen_910_ = v_ngen_933_;
v_auxDeclNGen_911_ = v_auxDeclNGen_934_;
v_traceState_912_ = v_traceState_935_;
v_recordedDeps_913_ = v_recordedDeps_936_;
v_messages_914_ = v_messages_937_;
v_infoState_915_ = v_infoState_938_;
v_snapshotTasks_916_ = v_snapshotTasks_939_;
v___y_917_ = v___x_948_;
goto v___jp_906_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc_ref_n(v_toEnvExtension_941_, 2);
v___x_949_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_941_, v_env_931_);
lean_dec_ref(v_env_931_);
v___x_950_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_941_, v___x_949_, v___f_947_, v_asyncMode_943_, v___x_895_, v___x_923_);
v___y_907_ = v___x_945_;
v___y_908_ = v___y_929_;
v_nextMacroScope_909_ = v_nextMacroScope_932_;
v_ngen_910_ = v_ngen_933_;
v_auxDeclNGen_911_ = v_auxDeclNGen_934_;
v_traceState_912_ = v_traceState_935_;
v_recordedDeps_913_ = v_recordedDeps_936_;
v_messages_914_ = v_messages_937_;
v_infoState_915_ = v_infoState_938_;
v_snapshotTasks_916_ = v_snapshotTasks_939_;
v___y_917_ = v___x_950_;
goto v___jp_906_;
}
}
v___jp_951_:
{
if (lean_obj_tag(v___y_955_) == 0)
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Linter_mkSinceHint(v_stx_901_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_a_959_);
v___x_962_ = l_Lean_logWarning___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__2(v___x_961_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v___y_925_ = v___y_952_;
v___y_926_ = v___y_954_;
v___y_927_ = v___y_953_;
v___y_928_ = v___y_955_;
v___y_929_ = v___y_957_;
goto v___jp_924_;
}
else
{
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v_declName_900_);
lean_dec(v___x_895_);
return v___x_962_;
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v_declName_900_);
lean_dec(v___x_895_);
v_a_963_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_958_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_958_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_dec(v_stx_901_);
v___y_925_ = v___y_952_;
v___y_926_ = v___y_954_;
v___y_927_ = v___y_953_;
v___y_928_ = v___y_955_;
v___y_929_ = v___y_957_;
goto v___jp_924_;
}
}
v___jp_971_:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_array_get_size(v___y_976_);
v___x_981_ = lean_nat_dec_lt(v___x_896_, v___x_980_);
lean_dec(v___x_896_);
if (v___x_981_ == 0)
{
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
v___y_952_ = v___y_972_;
v___y_953_ = v___y_974_;
v___y_954_ = v___y_973_;
v___y_955_ = v___y_977_;
v___y_956_ = v___y_978_;
v___y_957_ = v___y_979_;
goto v___jp_951_;
}
else
{
if (v___x_981_ == 0)
{
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
v___y_952_ = v___y_972_;
v___y_953_ = v___y_974_;
v___y_954_ = v___y_973_;
v___y_955_ = v___y_977_;
v___y_956_ = v___y_978_;
v___y_957_ = v___y_979_;
goto v___jp_951_;
}
else
{
size_t v___x_982_; size_t v___x_983_; uint8_t v___x_984_; 
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_980_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(v___y_972_, v___y_976_, v___x_982_, v___x_983_);
lean_dec_ref(v___y_976_);
if (v___x_984_ == 0)
{
lean_dec(v___y_975_);
v___y_952_ = v___y_972_;
v___y_953_ = v___y_974_;
v___y_954_ = v___y_973_;
v___y_955_ = v___y_977_;
v___y_956_ = v___y_978_;
v___y_957_ = v___y_979_;
goto v___jp_951_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v___y_977_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v_stx_901_);
lean_dec(v___x_895_);
v___x_985_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_986_ = l_Lean_MessageData_ofName(v___y_972_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_MessageData_ofName(v_declName_900_);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__7_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_MessageData_ofName(v___y_975_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__9_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_997_, v___y_978_, v___y_979_);
return v___x_998_;
}
}
}
}
v___jp_999_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
v___x_1008_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1009_ = l_Lean_MessageData_ofName(v___y_1005_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__11_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_MessageData_ofName(v_declName_900_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1008_);
v___x_1016_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1015_, v___y_1003_, v___y_1004_);
return v___x_1016_;
}
v___jp_1017_:
{
lean_object* v___x_1024_; 
lean_inc(v_declName_900_);
v___x_1024_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3(v_declName_900_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; uint8_t v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; uint64_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Lean_ConstantInfo_type(v_a_1025_);
lean_dec(v_a_1025_);
v___x_1027_ = 0;
v___x_1028_ = 1;
v___x_1029_ = 0;
v___x_1030_ = 2;
v___x_1031_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1031_, 0, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 1, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 2, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 3, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 4, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 5, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 6, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 7, v___x_1027_);
lean_ctor_set_uint8(v___x_1031_, 8, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 9, v___x_1028_);
lean_ctor_set_uint8(v___x_1031_, 10, v___x_1029_);
lean_ctor_set_uint8(v___x_1031_, 11, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 12, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 13, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 14, v___x_1030_);
lean_ctor_set_uint8(v___x_1031_, 15, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 16, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 17, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 18, v___x_923_);
lean_ctor_set_uint8(v___x_1031_, 19, v___x_1027_);
v___x_1032_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set_uint64(v___x_1033_, sizeof(void*)*1, v___x_1032_);
v___x_1034_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__12_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1035_ = lean_unsigned_to_nat(32u);
v___x_1036_ = lean_mk_empty_array_with_capacity(v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1_spec__1___closed__3);
v___x_1038_ = ((size_t)5ULL);
lean_inc_n(v___x_896_, 7);
v___x_1039_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1036_);
lean_ctor_set(v___x_1039_, 2, v___x_896_);
lean_ctor_set(v___x_1039_, 3, v___x_896_);
lean_ctor_set_usize(v___x_1039_, 4, v___x_1038_);
v___x_1040_ = lean_box(1);
lean_inc_ref(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1034_);
lean_ctor_set(v___x_1041_, 1, v___x_1039_);
lean_ctor_set(v___x_1041_, 2, v___x_1040_);
v___x_1042_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_1043_ = lean_box(0);
lean_inc(v___x_897_);
v___x_1044_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1044_, 0, v___x_1033_);
lean_ctor_set(v___x_1044_, 1, v___x_897_);
lean_ctor_set(v___x_1044_, 2, v___x_1041_);
lean_ctor_set(v___x_1044_, 3, v___x_1042_);
lean_ctor_set(v___x_1044_, 4, v___x_1043_);
lean_ctor_set(v___x_1044_, 5, v___x_896_);
lean_ctor_set(v___x_1044_, 6, v___x_1043_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*7, v___x_1027_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*7 + 1, v___x_1027_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*7 + 2, v___x_1027_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*7 + 3, v___x_923_);
v___x_1045_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1046_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1046_, 0, v___x_896_);
lean_ctor_set(v___x_1046_, 1, v___x_896_);
lean_ctor_set(v___x_1046_, 2, v___x_896_);
lean_ctor_set(v___x_1046_, 3, v___x_896_);
lean_ctor_set(v___x_1046_, 4, v___x_1034_);
lean_ctor_set(v___x_1046_, 5, v___x_1034_);
lean_ctor_set(v___x_1046_, 6, v___x_1034_);
lean_ctor_set(v___x_1046_, 7, v___x_1034_);
lean_ctor_set(v___x_1046_, 8, v___x_1034_);
lean_ctor_set(v___x_1046_, 9, v___x_1034_);
lean_ctor_set(v___x_1046_, 10, v___x_1034_);
lean_ctor_set(v___x_1046_, 11, v___x_1045_);
v___x_1047_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__13_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1048_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__14_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1046_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_897_);
lean_ctor_set(v___x_1049_, 3, v___x_1039_);
lean_ctor_set(v___x_1049_, 4, v___x_1048_);
v___x_1050_ = lean_st_mk_ref(v___x_1049_);
v___x_1051_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__4___redArg(v___x_1026_, v___f_898_, v___x_1027_, v___x_1027_, v___x_1044_, v___x_1050_, v___y_1021_, v___y_1022_);
lean_dec_ref_known(v___x_1044_, 7);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = lean_st_ref_get(v___x_1050_);
lean_dec(v___x_1050_);
lean_dec(v___x_1053_);
if (lean_obj_tag(v___y_1019_) == 1)
{
lean_object* v_val_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_val_1054_ = lean_ctor_get(v___y_1019_, 0);
lean_inc(v_val_1054_);
v___x_1055_ = lean_array_get_size(v_a_1052_);
v___x_1056_ = lean_nat_dec_lt(v___x_896_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v_stx_901_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___y_1000_ = v___y_1018_;
v___y_1001_ = v___y_1019_;
v___y_1002_ = v___y_1020_;
v___y_1003_ = v___y_1021_;
v___y_1004_ = v___y_1022_;
v___y_1005_ = v_val_1054_;
v___y_1006_ = v_a_1052_;
v___y_1007_ = v___y_1023_;
goto v___jp_999_;
}
else
{
if (v___x_1056_ == 0)
{
lean_dec(v_stx_901_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___y_1000_ = v___y_1018_;
v___y_1001_ = v___y_1019_;
v___y_1002_ = v___y_1020_;
v___y_1003_ = v___y_1021_;
v___y_1004_ = v___y_1022_;
v___y_1005_ = v_val_1054_;
v___y_1006_ = v_a_1052_;
v___y_1007_ = v___y_1023_;
goto v___jp_999_;
}
else
{
size_t v___x_1057_; size_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = lean_usize_of_nat(v___x_1055_);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(v_val_1054_, v_a_1052_, v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v_stx_901_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v___y_1000_ = v___y_1018_;
v___y_1001_ = v___y_1019_;
v___y_1002_ = v___y_1020_;
v___y_1003_ = v___y_1021_;
v___y_1004_ = v___y_1022_;
v___y_1005_ = v_val_1054_;
v___y_1006_ = v_a_1052_;
v___y_1007_ = v___y_1023_;
goto v___jp_999_;
}
else
{
v___y_972_ = v___y_1018_;
v___y_973_ = v___y_1020_;
v___y_974_ = v___y_1019_;
v___y_975_ = v_val_1054_;
v___y_976_ = v_a_1052_;
v___y_977_ = v___y_1023_;
v___y_978_ = v___y_1021_;
v___y_979_ = v___y_1022_;
goto v___jp_971_;
}
}
}
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_a_1052_);
v___x_1061_ = lean_nat_dec_lt(v___x_896_, v___x_1060_);
lean_dec(v___x_896_);
if (v___x_1061_ == 0)
{
lean_dec(v_a_1052_);
v___y_952_ = v___y_1018_;
v___y_953_ = v___y_1019_;
v___y_954_ = v___y_1020_;
v___y_955_ = v___y_1023_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
goto v___jp_951_;
}
else
{
if (v___x_1061_ == 0)
{
lean_dec(v_a_1052_);
v___y_952_ = v___y_1018_;
v___y_953_ = v___y_1019_;
v___y_954_ = v___y_1020_;
v___y_955_ = v___y_1023_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
goto v___jp_951_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1060_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__5(v___y_1018_, v_a_1052_, v___x_1062_, v___x_1063_);
lean_dec(v_a_1052_);
if (v___x_1064_ == 0)
{
v___y_952_ = v___y_1018_;
v___y_953_ = v___y_1019_;
v___y_954_ = v___y_1020_;
v___y_955_ = v___y_1023_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
goto v___jp_951_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v___y_1023_);
lean_dec(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec(v_stx_901_);
lean_dec(v___x_895_);
v___x_1065_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg___closed__3);
v___x_1066_ = l_Lean_MessageData_ofName(v___y_1018_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__5_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_ofName(v_declName_900_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1073_, v___y_1021_, v___y_1022_);
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v___x_1050_);
lean_dec(v___y_1023_);
lean_dec(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v_a_1075_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1051_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1051_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v___y_1023_);
lean_dec(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v_stx_901_);
lean_dec(v_declName_900_);
lean_dec_ref(v___f_898_);
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v___x_895_);
v_a_1083_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1024_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1024_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
v___jp_1091_:
{
if (lean_obj_tag(v___y_1094_) == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_box(0);
v___y_1018_ = v___y_1092_;
v___y_1019_ = v___y_1093_;
v___y_1020_ = v___y_1097_;
v___y_1021_ = v___y_1095_;
v___y_1022_ = v___y_1096_;
v___y_1023_ = v___x_1098_;
goto v___jp_1017_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
v_val_1099_ = lean_ctor_get(v___y_1094_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1094_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1101_ = v___y_1094_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v___y_1094_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lean_TSyntax_getString(v_val_1099_);
lean_dec(v_val_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1018_ = v___y_1092_;
v___y_1019_ = v___y_1093_;
v___y_1020_ = v___y_1097_;
v___y_1021_ = v___y_1095_;
v___y_1022_ = v___y_1096_;
v___y_1023_ = v___x_1105_;
goto v___jp_1017_;
}
}
}
}
v___jp_1108_:
{
if (lean_obj_tag(v___y_1113_) == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_box(0);
v___y_1092_ = v___y_1109_;
v___y_1093_ = v___y_1114_;
v___y_1094_ = v___y_1110_;
v___y_1095_ = v___y_1111_;
v___y_1096_ = v___y_1112_;
v___y_1097_ = v___x_1115_;
goto v___jp_1091_;
}
else
{
lean_object* v_val_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1127_; 
v_val_1116_ = lean_ctor_get(v___y_1113_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___y_1113_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1118_ = v___y_1113_;
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_val_1116_);
lean_dec(v___y_1113_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1127_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_TSyntax_getString(v_val_1116_);
lean_dec(v_val_1116_);
v___x_1121_ = lean_string_utf8_byte_size(v___x_1120_);
v___x_1122_ = lean_nat_dec_eq(v___x_1121_, v___x_896_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1120_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v___y_1092_ = v___y_1109_;
v___y_1093_ = v___y_1114_;
v___y_1094_ = v___y_1110_;
v___y_1095_ = v___y_1111_;
v___y_1096_ = v___y_1112_;
v___y_1097_ = v___x_1124_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1120_);
lean_del_object(v___x_1118_);
v___x_1126_ = lean_box(0);
v___y_1092_ = v___y_1109_;
v___y_1093_ = v___y_1114_;
v___y_1094_ = v___y_1110_;
v___y_1095_ = v___y_1111_;
v___y_1096_ = v___y_1112_;
v___y_1097_ = v___x_1126_;
goto v___jp_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v___x_1190_, lean_object* v___f_1191_, lean_object* v___x_1192_, lean_object* v_declName_1193_, lean_object* v_stx_1194_, lean_object* v___kind_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___kind_boxed_1199_; lean_object* v_res_1200_; 
v___kind_boxed_1199_ = lean_unbox(v___kind_1195_);
v_res_1200_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v___x_1186_, v___x_1187_, v___x_1188_, v___x_1189_, v___x_1190_, v___f_1191_, v___x_1192_, v_declName_1193_, v_stx_1194_, v___kind_boxed_1199_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___x_1192_);
return v_res_1200_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__0_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1203_ = l_Lean_stringToMessageData(v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__2_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(lean_object* v___x_1207_, lean_object* v_decl_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__1_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1213_ = l_Lean_MessageData_ofName(v___x_1207_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3___closed__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v___x_1216_, v___y_1209_, v___y_1210_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v___x_1218_, lean_object* v_decl_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___lam__3_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(v___x_1218_, v_decl_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_decl_1219_);
return v_res_1223_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_unsigned_to_nat(3307094584u);
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1267_ = l_Lean_Name_num___override(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1270_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1271_ = l_Lean_Name_str___override(v___x_1270_, v___x_1269_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1274_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1275_ = l_Lean_Name_str___override(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_unsigned_to_nat(2u);
v___x_1277_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1278_ = l_Lean_Name_num___override(v___x_1277_, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1293_ = 0;
v___x_1294_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1296_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1297_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1295_);
lean_ctor_set(v___x_1297_, 2, v___x_1294_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*3, v___x_1293_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___f_1298_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___f_1299_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_));
v___x_1300_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___f_1299_);
lean_ctor_set(v___x_1301_, 2, v___f_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_, &l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn___closed__29_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_);
v___x_1304_ = l_Lean_registerBuiltinAttribute(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2____boxed(lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(size_t v_sz_1307_, size_t v_i_1308_, lean_object* v_bs_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___redArg(v_sz_1307_, v_i_1308_, v_bs_1309_, v___y_1310_, v___y_1312_, v___y_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0___boxed(lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_bs_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__0(v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___redArg(v_msg_1328_, v___y_1329_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_msg_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_throwError___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__1(v_00_u03b1_1333_, v_msg_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_00_u03b1_1339_, lean_object* v_constName_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___redArg(v_constName_1340_, v___y_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_constName_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b1_1345_, v_constName_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1351_, lean_object* v_ref_1352_, lean_object* v_constName_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___redArg(v_ref_1352_, v_constName_1353_, v___y_1354_, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_ref_1359_, lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_00_u03b1_1358_, v_ref_1359_, v_constName_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v_ref_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b1_1365_, lean_object* v_ref_1366_, lean_object* v_msg_1367_, lean_object* v_declHint_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___redArg(v_ref_1366_, v_msg_1367_, v_declHint_1368_, v___y_1369_, v___y_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_ref_1374_, lean_object* v_msg_1375_, lean_object* v_declHint_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11(v_00_u03b1_1373_, v_ref_1374_, v_msg_1375_, v_declHint_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v_ref_1374_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(lean_object* v_msg_1381_, lean_object* v_declHint_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___redArg(v_msg_1381_, v_declHint_1382_, v___y_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__12_spec__13(v_msg_1387_, v_declHint_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(lean_object* v_00_u03b1_1393_, lean_object* v_ref_1394_, lean_object* v_msg_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___redArg(v_ref_1394_, v_msg_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_ref_1401_, lean_object* v_msg_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2__spec__3_spec__5_spec__8_spec__11_spec__13(v_00_u03b1_1400_, v_ref_1401_, v_msg_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_ref_1401_);
return v_res_1406_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_817751715____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_linter_deprecated_arg = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_linter_deprecated_arg);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_2070725456____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedArgExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedArgExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedArg_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedArg_3307094584____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedArg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedArg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedArg(builtin);
}
#ifdef __cplusplus
}
#endif
